(******************************************************************************)
(*                                                                            *)
(*              Deterministic Event-Stream Canonicalization                   *)
(*                                                                            *)
(*     Reduces a raw event stream — with duplicates, reordering, gaps,        *)
(*     corrections, and cancels — to a deterministic, idempotent canonical    *)
(*     truth stream.  Output is a sorted permutation with unique ids, no      *)
(*     cancel leakage, and ids drawn strictly from the input.  Online         *)
(*     ingestion via fold_stream equals batch canonicalization by             *)
(*     construction; chunked replay is compositional over append.             *)
(*     Replay-safe ingestion layer for bit-for-bit reproducible pipelines.    *)
(*                                                                            *)
(*     "No man ever steps in the same river twice, for it is not the          *)
(*     same river and he is not the same man."                                *)
(*     — Heraclitus, c. 500 BC                                               *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: February 10, 2026                                                *)
(*     License: Proprietary — All Rights Reserved                             *)
(*                                                                            *)
(*     Note on extraction: nat is mapped to OCaml int via ExtrOcamlNatInt.    *)
(*     Sort is bottom-up mergesort (O(n log n)) defined as direct fixpoints  *)
(*     inside the Section to avoid Module/Section incompatibility.           *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Structures.Orders.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Lia.
Require Import Coq.Lists.SetoidList.
Import ListNotations.

(** * Lexicographic comparison on nat lists. *)

Fixpoint lex_compare (l1 l2 : list nat) : comparison :=
  match l1, l2 with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | k1 :: rest1, k2 :: rest2 =>
    match Nat.compare k1 k2 with
    | Lt => Lt
    | Gt => Gt
    | Eq => lex_compare rest1 rest2
    end
  end.

Definition lex_leb (l1 l2 : list nat) : bool :=
  match lex_compare l1 l2 with
  | Gt => false
  | _ => true
  end.

Lemma lex_compare_refl
  : forall l, lex_compare l l = Eq.
Proof.
  induction l as [| k l' IH]; simpl.
  - reflexivity.
  - rewrite Nat.compare_refl. exact IH.
Qed.

Lemma lex_compare_antisym
  : forall l1 l2, lex_compare l1 l2 = CompOpp (lex_compare l2 l1).
Proof.
  induction l1 as [| a l1' IH]; intros [| b l2']; simpl; try reflexivity.
  rewrite Nat.compare_antisym.
  destruct (Nat.compare b a) eqn:Hba; simpl; try reflexivity.
  apply IH.
Qed.

Lemma lex_compare_eq
  : forall l1 l2, lex_compare l1 l2 = Eq -> l1 = l2.
Proof.
  induction l1 as [| a l1' IH]; intros [| b l2']; simpl; intro H;
    try reflexivity; try discriminate.
  destruct (Nat.compare a b) eqn:Hab; try discriminate.
  apply Nat.compare_eq_iff in Hab. subst b.
  f_equal. apply IH. exact H.
Qed.

Lemma lex_leb_refl
  : forall l, lex_leb l l = true.
Proof.
  intro l. unfold lex_leb. rewrite lex_compare_refl. reflexivity.
Qed.

Lemma lex_leb_total
  : forall l1 l2, lex_leb l1 l2 = true \/ lex_leb l2 l1 = true.
Proof.
  intros l1 l2. unfold lex_leb.
  rewrite lex_compare_antisym.
  destruct (lex_compare l2 l1); simpl; auto.
Qed.

Lemma lex_leb_antisym
  : forall l1 l2, lex_leb l1 l2 = true -> lex_leb l2 l1 = true -> l1 = l2.
Proof.
  intros l1 l2 H1 H2. unfold lex_leb in *.
  apply lex_compare_eq.
  destruct (lex_compare l1 l2) eqn:H12; try reflexivity; try discriminate.
  (* Lt case: lex_compare l2 l1 must be Gt by antisymmetry *)
  rewrite lex_compare_antisym, H12 in H2. simpl in H2. discriminate.
Qed.

Lemma lex_compare_not_gt_trans
  : forall l1 l2 l3,
    lex_compare l1 l2 <> Gt ->
    lex_compare l2 l3 <> Gt ->
    lex_compare l1 l3 <> Gt.
Proof.
  induction l1 as [| a l1' IH].
  - intros l2 l3 H12 H23. destruct l2; destruct l3; simpl; discriminate.
  - intros [| b l2'] [| c l3']; simpl; intros H12 H23.
    + exact H12.
    + exfalso. apply H12. reflexivity.
    + exfalso. apply H23. reflexivity.
    + destruct (Nat.compare a b) eqn:Hab.
      * apply Nat.compare_eq_iff in Hab. subst b.
        destruct (Nat.compare a c) eqn:Hac.
        -- apply Nat.compare_eq_iff in Hac. subst c.
           exact (IH _ _ H12 H23).
        -- intro; discriminate.
        -- exfalso. apply H23. reflexivity.
      * (* a < b, need a <= c *)
        apply Nat.compare_lt_iff in Hab.
        intro H13.
        assert (Hbc : b <= c).
        { destruct (Nat.compare_spec b c) as [Heq | Hlt | Hgt].
          - lia. - lia.
          - exfalso. exact (H23 eq_refl). }
        assert (Hac : (a ?= c) = Lt) by (apply Nat.compare_lt_iff; lia).
        rewrite Hac in H13. discriminate.
      * exfalso. apply H12. reflexivity.
Qed.

Lemma lex_leb_trans
  : forall l1 l2 l3,
    lex_leb l1 l2 = true -> lex_leb l2 l3 = true -> lex_leb l1 l3 = true.
Proof.
  intros l1 l2 l3 H1 H2. unfold lex_leb in *.
  destruct (lex_compare l1 l3) eqn:H13; try reflexivity.
  exfalso.
  apply (lex_compare_not_gt_trans l1 l2 l3).
  - destruct (lex_compare l1 l2); discriminate.
  - destruct (lex_compare l2 l3); discriminate.
  - exact H13.
Qed.

(** * Core types. *)

Inductive event_kind : Type :=
  | Original
  | Correction
  | Cancel.

(** * AVL map keyed by nat, used for the map-based accumulator.
    Defined outside the Section because Coq forbids Modules inside Sections. *)

Module IdMap := FMapAVL.Make(Nat_as_OT).

Section Parameterized.

Variable Key : Type.
Variable key_compare : Key -> Key -> comparison.
Variable key_eqb : Key -> Key -> bool.

Hypothesis key_compare_refl
  : forall k, key_compare k k = Eq.
Hypothesis key_compare_antisym
  : forall k1 k2, key_compare k1 k2 = CompOpp (key_compare k2 k1).
Hypothesis key_compare_eq
  : forall k1 k2, key_compare k1 k2 = Eq -> k1 = k2.
Hypothesis key_compare_not_gt_trans
  : forall k1 k2 k3,
    key_compare k1 k2 <> Gt ->
    key_compare k2 k3 <> Gt ->
    key_compare k1 k3 <> Gt.
Hypothesis key_eqb_spec
  : forall k1 k2, reflect (k1 = k2) (key_eqb k1 k2).

Lemma key_eqb_eq
  : forall k1 k2, key_eqb k1 k2 = true -> k1 = k2.
Proof.
  intros k1 k2 H. destruct (key_eqb_spec k1 k2) as [Heq | Hneq].
  - exact Heq.
  - discriminate.
Defined.

Lemma key_eqb_neq
  : forall k1 k2, key_eqb k1 k2 = false -> k1 <> k2.
Proof.
  intros k1 k2 H. destruct (key_eqb_spec k1 k2) as [Heq | Hneq].
  - discriminate.
  - exact Hneq.
Defined.

Variable Payload : Type.
Variable payload_compare : Payload -> Payload -> comparison.
Variable payload_eqb : Payload -> Payload -> bool.

Hypothesis payload_compare_refl
  : forall p, payload_compare p p = Eq.
Hypothesis payload_compare_antisym
  : forall p1 p2, payload_compare p1 p2 = CompOpp (payload_compare p2 p1).
Hypothesis payload_compare_eq
  : forall p1 p2, payload_compare p1 p2 = Eq -> p1 = p2.
Hypothesis payload_compare_not_gt_trans
  : forall p1 p2 p3,
    payload_compare p1 p2 <> Gt ->
    payload_compare p2 p3 <> Gt ->
    payload_compare p1 p3 <> Gt.
Hypothesis payload_eqb_spec
  : forall p1 p2, reflect (p1 = p2) (payload_eqb p1 p2).

Record event : Type := mkEvent {
  ev_id : Key;
  ev_timestamp : Key;
  ev_seq : Key;
  ev_payload : Payload;
  ev_kind : event_kind
}.

(** Conflict resolution: should_replace old_event new_event = true
    means the new event wins when both share the same id. *)
Variable should_replace : event -> event -> bool.

(** Cancel semantics: cancel_handler cancel_event accumulator returns
    the accumulator with the cancelled event's effects removed. *)
Variable cancel_handler : event -> list event -> list event.

Hypothesis cancel_handler_removes_id
  : forall e acc, ~ In (ev_id e) (map ev_id (cancel_handler e acc)).
Hypothesis cancel_handler_preserves_other_id
  : forall e acc id,
    ev_id e <> id ->
    In id (map ev_id (cancel_handler e acc)) <-> In id (map ev_id acc).
Hypothesis cancel_handler_no_cancels
  : forall e acc,
    (forall x, In x acc -> ev_kind x <> Cancel) ->
    (forall x, In x (cancel_handler e acc) -> ev_kind x <> Cancel).
Hypothesis cancel_handler_NoDup
  : forall e acc, NoDup (map ev_id acc) -> NoDup (map ev_id (cancel_handler e acc)).
Hypothesis cancel_handler_ids_incl
  : forall e acc, incl (map ev_id (cancel_handler e acc)) (map ev_id acc).
Hypothesis cancel_handler_preserves_event
  : forall e acc x,
    ev_id e <> ev_id x ->
    In x (cancel_handler e acc) <-> In x acc.

(** * Abstract map keyed by Key, used for the map-based accumulator.
    Concrete implementations (e.g. AVL via FMapAVL) are supplied
    at instantiation time. *)

Variable KMap : Type.
Variable kmap_find : Key -> KMap -> option event.
Variable kmap_add : Key -> event -> KMap -> KMap.
Variable kmap_remove : Key -> KMap -> KMap.
Variable kmap_In : Key -> KMap -> Prop.
Variable kmap_elements : KMap -> list (Key * event).

Hypothesis kmap_find_In
  : forall k m v, kmap_find k m = Some v -> kmap_In k m.
Hypothesis kmap_add_In_same
  : forall k v m, kmap_In k (kmap_add k v m).
Hypothesis kmap_add_In_other
  : forall k k' v m, k <> k' -> (kmap_In k' (kmap_add k v m) <-> kmap_In k' m).
Hypothesis kmap_remove_not_In
  : forall k m, ~ kmap_In k (kmap_remove k m).
Hypothesis kmap_remove_In_other
  : forall k k' m, k' <> k -> (kmap_In k' (kmap_remove k m) <-> kmap_In k' m).

Variable kmap_empty : KMap.
Hypothesis kmap_find_empty
  : forall k, kmap_find k kmap_empty = None.
Hypothesis kmap_find_add_same
  : forall k v m, kmap_find k (kmap_add k v m) = Some v.
Hypothesis kmap_find_add_other
  : forall k k' v m, k <> k' -> kmap_find k' (kmap_add k v m) = kmap_find k' m.
Hypothesis kmap_find_remove_same
  : forall k m, kmap_find k (kmap_remove k m) = None.
Hypothesis kmap_find_remove_other
  : forall k k' m, k' <> k -> kmap_find k' (kmap_remove k m) = kmap_find k' m.
Hypothesis kmap_elements_correct
  : forall k v m, In (k, v) (kmap_elements m) <-> kmap_find k m = Some v.
Hypothesis kmap_elements_NoDup
  : forall m, NoDup (map fst (kmap_elements m)).

(** * Decidable equality. *)

Definition event_kind_eqb (k1 k2 : event_kind) : bool :=
  match k1, k2 with
  | Original, Original => true
  | Correction, Correction => true
  | Cancel, Cancel => true
  | _, _ => false
  end.

Lemma event_kind_eqb_spec
  : forall k1 k2, reflect (k1 = k2) (event_kind_eqb k1 k2).
Proof.
  destruct k1; destruct k2; constructor; try reflexivity; discriminate.
Defined.

Definition event_eqb (e1 e2 : event) : bool :=
  key_eqb (ev_id e1) (ev_id e2) &&
  key_eqb (ev_timestamp e1) (ev_timestamp e2) &&
  key_eqb (ev_seq e1) (ev_seq e2) &&
  payload_eqb (ev_payload e1) (ev_payload e2) &&
  event_kind_eqb (ev_kind e1) (ev_kind e2).

Lemma event_eqb_spec
  : forall e1 e2, reflect (e1 = e2) (event_eqb e1 e2).
Proof.
  intros [id1 ts1 sq1 pl1 k1] [id2 ts2 sq2 pl2 k2].
  unfold event_eqb; simpl.
  destruct (key_eqb_spec id1 id2);
  destruct (key_eqb_spec ts1 ts2);
  destruct (key_eqb_spec sq1 sq2);
  destruct (payload_eqb_spec pl1 pl2);
  destruct (event_kind_eqb_spec k1 k2);
  constructor; try (subst; reflexivity);
  intro H; injection H; intros; contradiction.
Defined.

(** * Total order on events via lexicographic comparison.
    Breaks all ties: timestamp, seq, id, payload, kind.
    This makes the sort deterministic and enables the antisymmetry e1 = e2. *)

Definition kind_index (k : event_kind) : nat :=
  match k with
  | Original => 0
  | Correction => 1
  | Cancel => 2
  end.

Lemma kind_index_injective
  : forall k1 k2, kind_index k1 = kind_index k2 -> k1 = k2.
Proof.
  destruct k1; destruct k2; simpl; intro H; try reflexivity; discriminate.
Qed.

(** Field-by-field comparison threading payload_compare for the
    payload field.  Order: timestamp, seq, id, payload, kind. *)

Definition event_compare (e1 e2 : event) : comparison :=
  match key_compare (ev_timestamp e1) (ev_timestamp e2) with
  | Lt => Lt | Gt => Gt
  | Eq =>
    match key_compare (ev_seq e1) (ev_seq e2) with
    | Lt => Lt | Gt => Gt
    | Eq =>
      match key_compare (ev_id e1) (ev_id e2) with
      | Lt => Lt | Gt => Gt
      | Eq =>
        match payload_compare (ev_payload e1) (ev_payload e2) with
        | Lt => Lt | Gt => Gt
        | Eq =>
          Nat.compare (kind_index (ev_kind e1)) (kind_index (ev_kind e2))
        end
      end
    end
  end.

Definition event_leb (e1 e2 : event) : bool :=
  match event_compare e1 e2 with
  | Gt => false
  | _ => true
  end.

Lemma event_compare_refl
  : forall e, event_compare e e = Eq.
Proof.
  intros [id ts sq pl k]. unfold event_compare. simpl.
  rewrite key_compare_refl.
  rewrite key_compare_refl.
  rewrite key_compare_refl.
  rewrite payload_compare_refl.
  rewrite Nat.compare_refl.
  reflexivity.
Qed.

Lemma event_compare_antisym
  : forall e1 e2, event_compare e1 e2 = CompOpp (event_compare e2 e1).
Proof.
  intros [id1 ts1 sq1 pl1 k1] [id2 ts2 sq2 pl2 k2].
  unfold event_compare. simpl.
  rewrite key_compare_antisym.
  destruct (key_compare ts2 ts1) eqn:Hts; simpl; try reflexivity.
  rewrite key_compare_antisym.
  destruct (key_compare sq2 sq1) eqn:Hsq; simpl; try reflexivity.
  rewrite key_compare_antisym.
  destruct (key_compare id2 id1) eqn:Hid; simpl; try reflexivity.
  rewrite payload_compare_antisym.
  destruct (payload_compare pl2 pl1) eqn:Hpl; simpl; try reflexivity.
  rewrite Nat.compare_antisym.
  destruct (Nat.compare (kind_index k2) (kind_index k1)); simpl; reflexivity.
Qed.

Lemma event_compare_eq
  : forall e1 e2, event_compare e1 e2 = Eq -> e1 = e2.
Proof.
  intros [id1 ts1 sq1 pl1 k1] [id2 ts2 sq2 pl2 k2].
  unfold event_compare. simpl.
  destruct (key_compare ts1 ts2) eqn:Hts; try discriminate.
  apply key_compare_eq in Hts. subst ts2.
  destruct (key_compare sq1 sq2) eqn:Hsq; try discriminate.
  apply key_compare_eq in Hsq. subst sq2.
  destruct (key_compare id1 id2) eqn:Hid; try discriminate.
  apply key_compare_eq in Hid. subst id2.
  destruct (payload_compare pl1 pl2) eqn:Hpl; try discriminate.
  apply payload_compare_eq in Hpl. subst pl2.
  destruct (Nat.compare (kind_index k1) (kind_index k2)) eqn:Hk; try discriminate.
  apply Nat.compare_eq_iff in Hk. apply kind_index_injective in Hk. subst k2.
  intro. reflexivity.
Qed.

Lemma event_leb_refl
  : forall e, event_leb e e = true.
Proof.
  intro e. unfold event_leb. rewrite event_compare_refl. reflexivity.
Qed.

Lemma event_leb_total
  : forall e1 e2, event_leb e1 e2 = true \/ event_leb e2 e1 = true.
Proof.
  intros e1 e2. unfold event_leb.
  rewrite event_compare_antisym.
  destruct (event_compare e2 e1); simpl; auto.
Qed.

Lemma event_leb_antisym
  : forall e1 e2, event_leb e1 e2 = true -> event_leb e2 e1 = true -> e1 = e2.
Proof.
  intros e1 e2 H1 H2. unfold event_leb in *.
  apply event_compare_eq.
  destruct (event_compare e1 e2) eqn:H12; try reflexivity; try discriminate.
  rewrite event_compare_antisym, H12 in H2. simpl in H2. discriminate.
Qed.

(** Helper for transitivity. *)

Lemma nat_compare_not_gt_trans
  : forall a b c,
    Nat.compare a b <> Gt ->
    Nat.compare b c <> Gt ->
    Nat.compare a c <> Gt.
Proof.
  intros a b c H1 H2 H3.
  destruct (Nat.compare a b) eqn:E1; [ | | exfalso; apply H1; reflexivity ].
  - apply Nat.compare_eq_iff in E1. subst b. apply H2. exact H3.
  - destruct (Nat.compare b c) eqn:E2; [ | | exfalso; apply H2; reflexivity ].
    + apply Nat.compare_eq_iff in E2. subst c. rewrite E1 in H3. discriminate.
    + rewrite Nat.compare_lt_iff in E1.
      rewrite Nat.compare_lt_iff in E2.
      rewrite Nat.compare_gt_iff in H3.
      lia.
Qed.

Lemma event_compare_not_gt_trans
  : forall e1 e2 e3,
    event_compare e1 e2 <> Gt ->
    event_compare e2 e3 <> Gt ->
    event_compare e1 e3 <> Gt.
Proof.
  intros [id1 ts1 sq1 pl1 k1] [id2 ts2 sq2 pl2 k2] [id3 ts3 sq3 pl3 k3].
  unfold event_compare. simpl.
  intros H12 H23.
  destruct (key_compare ts1 ts2) eqn:Hts12;
    [ apply key_compare_eq in Hts12; subst ts2 |
    | exfalso; apply H12; reflexivity ].
  - destruct (key_compare ts1 ts3) eqn:Hts13;
      [ apply key_compare_eq in Hts13; subst ts3 |
        intro; discriminate
      | exfalso; apply H23; reflexivity ].
    destruct (key_compare sq1 sq2) eqn:Hsq12;
      [ apply key_compare_eq in Hsq12; subst sq2 |
      | exfalso; apply H12; reflexivity ].
    + destruct (key_compare sq1 sq3) eqn:Hsq13;
        [ apply key_compare_eq in Hsq13; subst sq3 |
          intro; discriminate
        | exfalso; apply H23; reflexivity ].
      destruct (key_compare id1 id2) eqn:Hid12;
        [ apply key_compare_eq in Hid12; subst id2 |
        | exfalso; apply H12; reflexivity ].
      * destruct (key_compare id1 id3) eqn:Hid13;
          [ apply key_compare_eq in Hid13; subst id3 |
            intro; discriminate
          | exfalso; apply H23; reflexivity ].
        destruct (payload_compare pl1 pl2) eqn:Hpl12;
          [ apply payload_compare_eq in Hpl12; subst pl2 |
          | exfalso; apply H12; reflexivity ].
        -- destruct (payload_compare pl1 pl3) eqn:Hpl13;
             [ apply payload_compare_eq in Hpl13; subst pl3 |
               intro; discriminate
             | exfalso; apply H23; reflexivity ].
           apply nat_compare_not_gt_trans with (kind_index k2); assumption.
        -- destruct (payload_compare pl1 pl3) eqn:Hpl13.
           ++ apply payload_compare_eq in Hpl13. subst pl3.
              exfalso. apply H23.
              rewrite payload_compare_antisym. rewrite Hpl12. simpl.
              reflexivity.
           ++ intro Hc. discriminate.
           ++ exfalso.
              apply (payload_compare_not_gt_trans pl1 pl2 pl3).
              ** intro Hc. rewrite Hc in Hpl12. discriminate.
              ** destruct (payload_compare pl2 pl3) eqn:Hpl23;
                   try (intro Hc; discriminate).
                 exfalso; apply H23; reflexivity.
              ** exact Hpl13.
      * destruct (key_compare id1 id3) eqn:Hid13.
        -- apply key_compare_eq in Hid13. subst id3.
           exfalso. apply H23.
           rewrite key_compare_antisym. rewrite Hid12. simpl.
           reflexivity.
        -- intro Hc. discriminate.
        -- exfalso.
           apply (key_compare_not_gt_trans id1 id2 id3).
           ++ intro Hc. rewrite Hc in Hid12. discriminate.
           ++ destruct (key_compare id2 id3) eqn:Hid23;
                try (intro Hc; discriminate).
              exfalso; apply H23; reflexivity.
           ++ exact Hid13.
    + destruct (key_compare sq1 sq3) eqn:Hsq13.
      * apply key_compare_eq in Hsq13. subst sq3.
        exfalso. apply H23.
        rewrite key_compare_antisym. rewrite Hsq12. simpl.
        reflexivity.
      * intro Hc. discriminate.
      * exfalso.
        apply (key_compare_not_gt_trans sq1 sq2 sq3).
        -- intro Hc. rewrite Hc in Hsq12. discriminate.
        -- destruct (key_compare sq2 sq3) eqn:Hsq23;
             try (intro Hc; discriminate).
           exfalso; apply H23; reflexivity.
        -- exact Hsq13.
  - destruct (key_compare ts1 ts3) eqn:Hts13.
    + apply key_compare_eq in Hts13. subst ts3.
      exfalso. apply H23.
      rewrite key_compare_antisym. rewrite Hts12. simpl.
      reflexivity.
    + intro Hc. discriminate.
    + exfalso.
      apply (key_compare_not_gt_trans ts1 ts2 ts3).
      * intro Hc. rewrite Hc in Hts12. discriminate.
      * destruct (key_compare ts2 ts3) eqn:Hts23;
          try (intro Hc; discriminate).
        exfalso; apply H23; reflexivity.
      * exact Hts13.
Qed.

Lemma event_leb_trans
  : forall e1 e2 e3,
    event_leb e1 e2 = true -> event_leb e2 e3 = true -> event_leb e1 e3 = true.
Proof.
  intros e1 e2 e3 H1 H2. unfold event_leb in *.
  destruct (event_compare e1 e3) eqn:H13; try reflexivity.
  exfalso.
  apply (event_compare_not_gt_trans e1 e2 e3).
  - destruct (event_compare e1 e2); discriminate.
  - destruct (event_compare e2 e3); discriminate.
  - exact H13.
Qed.

(** * Mergesort on events.
    Bottom-up mergesort via a stack of sorted runs, following the
    algorithm of Coq.Sorting.Mergesort.  Defined directly as fixpoints
    to avoid Module/Section incompatibility. *)

Fixpoint merge (l1 : list event) : list event -> list event :=
  match l1 with
  | [] => fun l2 => l2
  | a1 :: l1' =>
    fix merge_aux (l2 : list event) : list event :=
      match l2 with
      | [] => a1 :: l1'
      | a2 :: l2' =>
        if event_leb a1 a2 then a1 :: merge l1' (a2 :: l2')
        else a2 :: merge_aux l2'
      end
  end.

Fixpoint merge_list_to_stack (stack : list (option (list event)))
    (l : list event) : list (option (list event)) :=
  match stack with
  | [] => [Some l]
  | None :: stack' => Some l :: stack'
  | Some l' :: stack' => None :: merge_list_to_stack stack' (merge l' l)
  end.

Fixpoint merge_stack (stack : list (option (list event)))
    : list event :=
  match stack with
  | [] => []
  | None :: stack' => merge_stack stack'
  | Some l :: stack' => merge l (merge_stack stack')
  end.

Fixpoint iter_merge (stack : list (option (list event)))
    (l : list event) : list event :=
  match l with
  | [] => merge_stack stack
  | a :: l' => iter_merge (merge_list_to_stack stack [a]) l'
  end.

Definition sort_events (l : list event) : list event :=
  iter_merge [] l.

(** * Sort correctness: output is a sorted permutation. *)

Inductive Sorted_leb : list event -> Prop :=
  | Sorted_leb_nil : Sorted_leb []
  | Sorted_leb_one : forall e, Sorted_leb [e]
  | Sorted_leb_cons : forall e1 e2 l,
      event_leb e1 e2 = true ->
      Sorted_leb (e2 :: l) ->
      Sorted_leb (e1 :: e2 :: l).

Lemma Sorted_leb_tail
  : forall e l, Sorted_leb (e :: l) -> Sorted_leb l.
Proof.
  intros e l Hs. inversion Hs; subst.
  - constructor.
  - assumption.
Defined.

Lemma Sorted_leb_head_leb
  : forall e1 e2 l, Sorted_leb (e1 :: e2 :: l) -> event_leb e1 e2 = true.
Proof.
  intros e1 e2 l Hs. inversion Hs; subst. assumption.
Defined.

Lemma Sorted_leb_from_head_sorted
  : forall a l,
    (match l with [] => True | h :: _ => event_leb a h = true end) ->
    Sorted_leb l ->
    Sorted_leb (a :: l).
Proof.
  intros a [| h t] Hh Hs.
  - apply Sorted_leb_one.
  - apply Sorted_leb_cons; assumption.
Defined.

(** ** Merge correctness. *)

Lemma merge_perm
  : forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [| a1 l1' IH1]; simpl; intro l2.
  - apply Permutation_refl.
  - induction l2 as [| a2 l2' IH2]; simpl.
    + rewrite app_nil_r. apply Permutation_refl.
    + destruct (event_leb a1 a2) eqn:Hleb.
      * apply perm_skip. apply IH1.
      * eapply Permutation_trans.
        -- exact (Permutation_sym (Permutation_middle (a1 :: l1') l2' a2)).
        -- apply perm_skip. exact IH2.
Defined.

Lemma merge_head_leb
  : forall l1 l2 a,
    (match l1 with [] => True | h :: _ => event_leb a h = true end) ->
    (match l2 with [] => True | h :: _ => event_leb a h = true end) ->
    match merge l1 l2 with [] => True | h :: _ => event_leb a h = true end.
Proof.
  intros [| a1 l1']; simpl.
  - intros l2 a _ H. exact H.
  - intros [| a2 l2'] a H1 H2; simpl.
    + exact H1.
    + destruct (event_leb a1 a2); [exact H1 | exact H2].
Defined.

Lemma merge_sorted
  : forall l1 l2,
    Sorted_leb l1 -> Sorted_leb l2 -> Sorted_leb (merge l1 l2).
Proof.
  induction l1 as [| a1 l1' IH1]; simpl; intros l2 Hs1 Hs2.
  - exact Hs2.
  - revert Hs2. induction l2 as [| a2 l2' IH2]; intro Hs2; simpl.
    + exact Hs1.
    + destruct (event_leb a1 a2) eqn:Hleb.
      * apply Sorted_leb_from_head_sorted.
        -- apply (merge_head_leb l1' (a2 :: l2') a1).
           ++ destruct l1' as [| b1 l1''].
              ** exact I.
              ** exact (Sorted_leb_head_leb a1 b1 l1'' Hs1).
           ++ simpl. exact Hleb.
        -- apply IH1.
           ++ exact (Sorted_leb_tail a1 l1' Hs1).
           ++ exact Hs2.
      * apply Sorted_leb_from_head_sorted.
        -- apply (merge_head_leb (a1 :: l1') l2' a2).
           ++ simpl. destruct (event_leb_total a1 a2) as [H | H].
              ** rewrite H in Hleb. discriminate.
              ** exact H.
           ++ destruct l2' as [| b2 l2''].
              ** exact I.
              ** exact (Sorted_leb_head_leb a2 b2 l2'' Hs2).
        -- apply IH2. exact (Sorted_leb_tail a2 l2' Hs2).
Defined.

(** ** Stack-based mergesort correctness. *)

Definition flatten_stack (s : list (option (list event)))
    : list event :=
  flat_map (fun o => match o with Some l => l | None => [] end) s.

Definition stack_sorted (s : list (option (list event)))
    : Prop :=
  forall l, In (Some l) s -> Sorted_leb l.

Lemma merge_list_to_stack_perm
  : forall s l,
    Permutation (l ++ flatten_stack s)
                (flatten_stack (merge_list_to_stack s l)).
Proof.
  induction s as [| [l' |] s' IH]; simpl; intro l.
  - rewrite app_nil_r. apply Permutation_refl.
  - eapply Permutation_trans; [| exact (IH (merge l' l))].
    rewrite app_assoc.
    apply Permutation_app_tail.
    eapply Permutation_trans.
    + apply Permutation_app_comm.
    + apply merge_perm.
  - apply Permutation_refl.
Defined.

Lemma merge_list_to_stack_sorted
  : forall s l,
    stack_sorted s -> Sorted_leb l ->
    stack_sorted (merge_list_to_stack s l).
Proof.
  induction s as [| [l' |] s' IH]; simpl; intros l Hss Hsl.
  - intros x [H | []]. injection H; intro; subst. exact Hsl.
  - intros x Hin. simpl in Hin.
    destruct Hin as [Habs | Hin]; [discriminate |].
    assert (Hss' : stack_sorted s').
    { intros y Hy. apply Hss. right. exact Hy. }
    assert (Hsml : Sorted_leb (merge l' l)).
    { apply merge_sorted; [apply Hss; left; reflexivity | exact Hsl]. }
    exact (IH (merge l' l) Hss' Hsml x Hin).
  - intros x [H | Hin].
    + injection H; intro; subst. exact Hsl.
    + apply Hss. right. exact Hin.
Defined.

Lemma merge_stack_perm
  : forall s, Permutation (flatten_stack s) (merge_stack s).
Proof.
  induction s as [| [l |] s' IH]; simpl.
  - apply Permutation_refl.
  - eapply Permutation_trans.
    + apply Permutation_app_head. exact IH.
    + apply merge_perm.
  - exact IH.
Defined.

Lemma merge_stack_sorted
  : forall s, stack_sorted s -> Sorted_leb (merge_stack s).
Proof.
  induction s as [| [l |] s' IH]; simpl; intro Hss.
  - apply Sorted_leb_nil.
  - apply merge_sorted.
    + apply Hss. left. reflexivity.
    + apply IH. intros y Hy. apply Hss. right. exact Hy.
  - apply IH. intros y Hy. apply Hss. right. exact Hy.
Defined.

Lemma iter_merge_perm
  : forall l s,
    Permutation (l ++ flatten_stack s) (iter_merge s l).
Proof.
  induction l as [| a l' IH]; simpl; intro s.
  - apply merge_stack_perm.
  - eapply Permutation_trans; [| exact (IH (merge_list_to_stack s [a]))].
    eapply Permutation_trans.
    + apply Permutation_middle.
    + apply Permutation_app_head. exact (merge_list_to_stack_perm s [a]).
Defined.

Lemma iter_merge_sorted
  : forall l s,
    stack_sorted s -> Sorted_leb (iter_merge s l).
Proof.
  induction l as [| a l' IH]; simpl; intros s Hss.
  - apply merge_stack_sorted. exact Hss.
  - apply IH. apply merge_list_to_stack_sorted.
    + exact Hss.
    + apply Sorted_leb_one.
Defined.

Theorem sort_events_perm
  : forall l, Permutation l (sort_events l).
Proof.
  intro l. unfold sort_events.
  rewrite <- (app_nil_r l) at 1.
  exact (iter_merge_perm l []).
Defined.

Theorem sort_events_sorted
  : forall l, Sorted_leb (sort_events l).
Proof.
  intro l. unfold sort_events.
  apply iter_merge_sorted.
  intros x [].
Defined.

(** * Sort helpers. *)

Lemma Sorted_leb_In_leb
  : forall a l x, Sorted_leb (a :: l) -> In x l -> event_leb a x = true.
Proof.
  intros a l. revert a.
  induction l as [| b l' IH]; intros a x Hs Hin.
  - destruct Hin.
  - destruct Hin as [<- | Hin].
    + exact (Sorted_leb_head_leb a b l' Hs).
    + apply event_leb_trans with b.
      * exact (Sorted_leb_head_leb a b l' Hs).
      * apply IH.
        -- exact (Sorted_leb_tail a (b :: l') Hs).
        -- exact Hin.
Defined.

(** * Sort uniqueness: a sorted permutation under total order is unique. *)

Theorem sort_unique
  : forall l1 l2,
    Sorted_leb l1 -> Sorted_leb l2 -> Permutation l1 l2 -> l1 = l2.
Proof.
  induction l1 as [| a l1' IH]; intros l2 Hs1 Hs2 Hp.
  - apply Permutation_nil in Hp. symmetry. exact Hp.
  - destruct l2 as [| b l2'].
    + apply Permutation_sym in Hp. apply Permutation_nil in Hp. discriminate.
    + assert (Ha_in : In a (b :: l2')).
      { apply (Permutation_in a Hp). left. reflexivity. }
      assert (Hb_in : In b (a :: l1')).
      { apply (Permutation_in b (Permutation_sym Hp)). left. reflexivity. }
      assert (Hab : event_leb a b = true).
      { destruct Hb_in as [<- | Hin].
        - apply event_leb_refl.
        - apply Sorted_leb_In_leb with l1'; assumption. }
      assert (Hba : event_leb b a = true).
      { destruct Ha_in as [<- | Hin].
        - apply event_leb_refl.
        - apply Sorted_leb_In_leb with l2'; assumption. }
      assert (Heq : a = b) by (apply event_leb_antisym; assumption).
      subst b. f_equal.
      apply IH.
      * exact (Sorted_leb_tail a l1' Hs1).
      * exact (Sorted_leb_tail a l2' Hs2).
      * apply Permutation_cons_inv with a. exact Hp.
Defined.

Lemma sort_sorted_id
  : forall l, Sorted_leb l -> sort_events l = l.
Proof.
  intros l Hs.
  apply sort_unique.
  - apply sort_events_sorted.
  - exact Hs.
  - apply Permutation_sym. apply sort_events_perm.
Defined.

(** * Determinism: canonicalize is permutation-invariant. *)

Lemma sort_events_deterministic
  : forall l1 l2, Permutation l1 l2 -> sort_events l1 = sort_events l2.
Proof.
  intros l1 l2 Hp.
  apply sort_unique.
  - apply sort_events_sorted.
  - apply sort_events_sorted.
  - apply Permutation_trans with l1.
    + apply Permutation_sym. apply sort_events_perm.
    + apply Permutation_trans with l2.
      * exact Hp.
      * apply sort_events_perm.
Defined.

(** * Last event for an id in a stream. *)

Fixpoint last_with_id (id : Key) (stream : list event) : option event :=
  match stream with
  | [] => None
  | e :: rest =>
    match last_with_id id rest with
    | Some e' => Some e'
    | None => if key_eqb (ev_id e) id then Some e else None
    end
  end.

Lemma last_with_id_None
  : forall id stream,
    last_with_id id stream = None ->
    forall e, In e stream -> ev_id e <> id.
Proof.
  intros id stream. revert id.
  induction stream as [| h t IH]; simpl; intros id Hlast e Hin.
  - destruct Hin.
  - destruct (last_with_id id t) eqn:Ht; [ discriminate | ].
    destruct (key_eqb (ev_id h) id) eqn:Heq; [ discriminate | ].
    destruct Hin as [<- | Hin].
    + apply key_eqb_neq. exact Heq.
    + exact (IH id Ht e Hin).
Defined.

(** * Event processing. *)

Fixpoint replace_or_add (e : event) (acc : list event) : list event :=
  match acc with
  | [] => [e]
  | h :: t =>
    if key_eqb (ev_id h) (ev_id e) then
      if should_replace h e then e :: t
      else h :: t
    else h :: replace_or_add e t
  end.

Fixpoint apply_events (sorted : list event) (acc : list event) : list event :=
  match sorted with
  | [] => acc
  | e :: rest =>
    match ev_kind e with
    | Original => apply_events rest (replace_or_add e acc)
    | Correction => apply_events rest (replace_or_add e acc)
    | Cancel =>
      apply_events rest (cancel_handler e acc)
    end
  end.

(** * Map-based accumulator (O(n log n) via AVL).
    The list-based apply_events above is the proven specification.
    For extraction we provide an equivalent map-based implementation.
    Equivalence is established via the shared semantic spec: both
    satisfy apply_events_spec / apply_events_map_spec, so their
    outputs are identical after sorting (by sort_unique). *)

Definition replace_or_add_map (e : event) (m : KMap) : KMap :=
  match kmap_find (ev_id e) m with
  | Some old => if should_replace old e
                then kmap_add (ev_id e) e m
                else m
  | None => kmap_add (ev_id e) e m
  end.

Fixpoint apply_events_map (sorted : list event) (m : KMap) : KMap :=
  match sorted with
  | [] => m
  | e :: rest =>
    match ev_kind e with
    | Original => apply_events_map rest (replace_or_add_map e m)
    | Correction => apply_events_map rest (replace_or_add_map e m)
    | Cancel => apply_events_map rest (kmap_remove (ev_id e) m)
    end
  end.

Definition map_values (m : KMap) : list event :=
  map snd (kmap_elements m).

(** Map-based helpers for the semantic spec proof. *)

Lemma replace_or_add_map_In_id
  : forall e m, kmap_In (ev_id e) (replace_or_add_map e m).
Proof.
  intros e m. unfold replace_or_add_map.
  destruct (kmap_find (ev_id e) m) as [old |] eqn:Hf.
  - destruct (should_replace old e).
    + apply kmap_add_In_same.
    + apply kmap_find_In with old. exact Hf.
  - apply kmap_add_In_same.
Defined.

Lemma replace_or_add_map_other
  : forall e m id,
    ev_id e <> id ->
    kmap_In id (replace_or_add_map e m) <-> kmap_In id m.
Proof.
  intros e m id Hne. unfold replace_or_add_map.
  destruct (kmap_find (ev_id e) m) as [old |] eqn:Hf.
  - destruct (should_replace old e).
    + apply kmap_add_In_other. exact Hne.
    + split; intro H; exact H.
  - apply kmap_add_In_other. exact Hne.
Defined.

Lemma remove_In_other
  : forall id id' (m : KMap),
    id' <> id ->
    kmap_In id' (kmap_remove id m) <-> kmap_In id' m.
Proof.
  intros id id' m Hne. apply kmap_remove_In_other. exact Hne.
Defined.

Lemma remove_not_In
  : forall id (m : KMap), ~ kmap_In id (kmap_remove id m).
Proof.
  intros id m. apply kmap_remove_not_In.
Defined.

Lemma apply_events_map_no_id_transparent
  : forall stream (m : KMap) id,
    (forall e, In e stream -> ev_id e <> id) ->
    kmap_In id (apply_events_map stream m) <-> kmap_In id m.
Proof.
  induction stream as [| e rest IH]; simpl; intros m id Hall.
  - split; intro H; exact H.
  - assert (Hne : ev_id e <> id) by (apply Hall; left; reflexivity).
    assert (Hrest : forall x, In x rest -> ev_id x <> id)
      by (intros x Hx; apply Hall; right; exact Hx).
    destruct (ev_kind e) eqn:Hk.
    + rewrite IH by exact Hrest.
      apply replace_or_add_map_other. exact Hne.
    + rewrite IH by exact Hrest.
      apply replace_or_add_map_other. exact Hne.
    + rewrite IH by exact Hrest.
      apply remove_In_other. intro Hc. apply Hne. symmetry. exact Hc.
Defined.

(** The map-based apply_events satisfies the same semantic spec
    as the list-based version. *)

Theorem apply_events_map_spec
  : forall stream (m : KMap) id,
    kmap_In id (apply_events_map stream m) <->
    match last_with_id id stream with
    | None => kmap_In id m
    | Some e => ev_kind e <> Cancel
    end.
Proof.
  induction stream as [| e rest IH]; simpl; intros m id.
  - split; intro H; exact H.
  - destruct (last_with_id id rest) eqn:Hlast.
    + destruct (ev_kind e) eqn:Hk.
      * specialize (IH (replace_or_add_map e m) id).
        rewrite Hlast in IH. exact IH.
      * specialize (IH (replace_or_add_map e m) id).
        rewrite Hlast in IH. exact IH.
      * specialize (IH (kmap_remove (ev_id e) m) id).
        rewrite Hlast in IH. exact IH.
    + assert (Hrest : forall x, In x rest -> ev_id x <> id)
        by (intros x Hx; exact (last_with_id_None id rest Hlast x Hx)).
      destruct (key_eqb (ev_id e) id) eqn:Heq.
      * apply key_eqb_eq in Heq. subst id.
        destruct (ev_kind e) eqn:Hk.
        -- rewrite apply_events_map_no_id_transparent by exact Hrest.
           split; [ intro; discriminate | ].
           intro. apply replace_or_add_map_In_id.
        -- rewrite apply_events_map_no_id_transparent by exact Hrest.
           split; [ intro; discriminate | ].
           intro. apply replace_or_add_map_In_id.
        -- rewrite apply_events_map_no_id_transparent by exact Hrest.
           split; [ intro Hin; exfalso; exact (remove_not_In (ev_id e) m Hin) | ].
           intro Habs. exfalso. apply Habs. reflexivity.
      * apply key_eqb_neq in Heq.
        destruct (ev_kind e) eqn:Hk.
        -- rewrite apply_events_map_no_id_transparent by exact Hrest.
           apply replace_or_add_map_other. exact Heq.
        -- rewrite apply_events_map_no_id_transparent by exact Hrest.
           apply replace_or_add_map_other. exact Heq.
        -- rewrite apply_events_map_no_id_transparent by exact Hrest.
           apply remove_In_other. intro Hc. apply Heq. symmetry. exact Hc.
Defined.

(** * Map-list equivalence.
    The list-based apply_events and the map-based apply_events_map
    produce the same result when started from empty.  The bridge is a
    pointwise invariant: for every key, kmap_find agrees with the
    unique list entry (if any). *)

Definition map_list_agree (acc : list event) (m : KMap) : Prop :=
  NoDup (map ev_id acc) /\
  (forall e, In e acc -> kmap_find (ev_id e) m = Some e) /\
  (forall id e, kmap_find id m = Some e -> In e acc).

Lemma map_list_agree_empty
  : map_list_agree [] kmap_empty.
Proof.
  split; [| split].
  - apply NoDup_nil.
  - intros e [].
  - intros id e H. rewrite kmap_find_empty in H. discriminate.
Defined.

(** Helper: replace_or_add is transparent for events with a different id. *)

Lemma replace_or_add_preserves_other
  : forall e acc x,
    ev_id e <> ev_id x ->
    In x (replace_or_add e acc) <-> In x acc.
Proof.
  intros e acc x Hne. induction acc as [| h t IH]; simpl.
  - split.
    + intros [H | []]. subst. exfalso. exact (Hne eq_refl).
    + intros [].
  - destruct (key_eqb (ev_id h) (ev_id e)) eqn:Heq.
    + apply key_eqb_eq in Heq.
      destruct (should_replace h e); simpl.
      * split.
        -- intros [H | H]; [subst; exfalso; exact (Hne eq_refl) | right; exact H].
        -- intros [H | H]; [subst; exfalso; apply Hne; symmetry; exact Heq | right; exact H].
      * tauto.
    + simpl. rewrite IH. tauto.
Defined.

(** Helper: replace_or_add_map at a different key is transparent. *)

Lemma kmap_find_replace_or_add_map_other
  : forall e m id,
    ev_id e <> id ->
    kmap_find id (replace_or_add_map e m) = kmap_find id m.
Proof.
  intros e m id Hne. unfold replace_or_add_map.
  destruct (kmap_find (ev_id e) m) as [old |].
  - destruct (should_replace old e).
    + apply kmap_find_add_other. exact Hne.
    + reflexivity.
  - apply kmap_find_add_other. exact Hne.
Defined.

(** Helper: replace_or_add_map at the same key. *)

Lemma kmap_find_replace_or_add_map_same
  : forall e m,
    kmap_find (ev_id e) (replace_or_add_map e m) =
    match kmap_find (ev_id e) m with
    | Some old => if should_replace old e then Some e else Some old
    | None => Some e
    end.
Proof.
  intros e m. unfold replace_or_add_map.
  destruct (kmap_find (ev_id e) m) as [old |] eqn:Hf.
  - destruct (should_replace old e) eqn:Hsr.
    + apply kmap_find_add_same.
    + exact Hf.
  - apply kmap_find_add_same.
Defined.

(** * The canonicalizer. *)

Definition canonicalize (stream : list event) : list event :=
  sort_events (apply_events (sort_events stream) []).

Theorem canonicalize_deterministic
  : forall s1 s2, Permutation s1 s2 -> canonicalize s1 = canonicalize s2.
Proof.
  intros s1 s2 Hp. unfold canonicalize.
  rewrite (sort_events_deterministic s1 s2 Hp). reflexivity.
Defined.

(** * Incremental processing: apply_events is compositional over append. *)

Lemma apply_events_app
  : forall s1 s2 acc,
    apply_events (s1 ++ s2) acc = apply_events s2 (apply_events s1 acc).
Proof.
  induction s1 as [| e rest IH]; simpl; intros s2 acc.
  - reflexivity.
  - destruct (ev_kind e); apply IH.
Defined.

(** * No cancel events survive apply_events. *)

Definition no_cancels (l : list event) : Prop :=
  forall e, In e l -> ev_kind e <> Cancel.

Lemma replace_or_add_no_cancels
  : forall e acc,
    ev_kind e <> Cancel -> no_cancels acc -> no_cancels (replace_or_add e acc).
Proof.
  intros e acc Hk Hacc.
  induction acc as [| h t IH]; simpl.
  - intros x [Hx | []]. subst. exact Hk.
  - destruct (key_eqb (ev_id h) (ev_id e)).
    + destruct (should_replace h e).
      * intros x [Hx | Hx]; [ subst; exact Hk | apply Hacc; right; exact Hx ].
      * intros x [Hx | Hx]; [ subst; apply Hacc; left; reflexivity | apply Hacc; right; exact Hx ].
    + intros x [Hx | Hx].
      * subst. apply Hacc. left. reflexivity.
      * apply IH; [ intros y Hy; apply Hacc; right; exact Hy | exact Hx ].
Defined.

Lemma filter_no_cancels
  : forall f acc, no_cancels acc -> no_cancels (filter f acc).
Proof.
  intros f acc Hacc.
  induction acc as [| h t IH]; simpl.
  - intros x [].
  - destruct (f h) eqn:Hfh.
    + intros x [Hx | Hx].
      * subst. apply Hacc. left. reflexivity.
      * apply IH; [ intros y Hy; apply Hacc; right; exact Hy | exact Hx ].
    + apply IH. intros y Hy. apply Hacc. right. exact Hy.
Defined.

Lemma apply_events_no_cancels
  : forall stream acc, no_cancels acc -> no_cancels (apply_events stream acc).
Proof.
  intros stream. induction stream as [| e rest IH]; simpl; intros acc Hacc.
  - exact Hacc.
  - destruct (ev_kind e) eqn:Hk.
    + apply IH. apply replace_or_add_no_cancels; [ rewrite Hk; discriminate | exact Hacc ].
    + apply IH. apply replace_or_add_no_cancels; [ rewrite Hk; discriminate | exact Hacc ].
    + apply IH. intros x Hx. apply (cancel_handler_no_cancels e acc Hacc x Hx).
Defined.

(** * Unique ids in output. *)

Definition ids_of (l : list event) : list Key := map ev_id l.

Lemma replace_or_add_on_fresh_id
  : forall e acc,
    ~ In (ev_id e) (ids_of acc) -> replace_or_add e acc = acc ++ [e].
Proof.
  intros e acc. induction acc as [| h t IH]; simpl; intro Hfresh.
  - reflexivity.
  - destruct (key_eqb (ev_id h) (ev_id e)) eqn:Heq.
    + apply key_eqb_eq in Heq. exfalso. apply Hfresh. left. exact Heq.
    + f_equal. apply IH. intro Hin. apply Hfresh. right. exact Hin.
Defined.

Lemma replace_or_add_ids
  : forall e acc,
    ids_of (replace_or_add e acc) =
    if existsb (fun x => key_eqb (ev_id x) (ev_id e)) acc
    then ids_of acc
    else ids_of acc ++ [ev_id e].
Proof.
  intros e acc. induction acc as [| h t IH]; simpl.
  - reflexivity.
  - destruct (key_eqb (ev_id h) (ev_id e)) eqn:Heq; simpl.
    + destruct (should_replace h e); simpl.
      * unfold ids_of. simpl. apply key_eqb_eq in Heq. rewrite Heq. reflexivity.
      * reflexivity.
    + unfold ids_of in *. simpl.
      rewrite IH.
      destruct (existsb (fun x => key_eqb (ev_id x) (ev_id e)) t); reflexivity.
Defined.

Lemma NoDup_replace_or_add
  : forall e acc, NoDup (ids_of acc) -> NoDup (ids_of (replace_or_add e acc)).
Proof.
  intros e acc Hnd. induction acc as [| h t IH]; simpl.
  - apply NoDup_cons. { simpl. auto. } apply NoDup_nil.
  - destruct (key_eqb (ev_id h) (ev_id e)) eqn:Heq.
    + destruct (should_replace h e).
      * apply key_eqb_eq in Heq.
        unfold ids_of. simpl.
        inversion Hnd; subst. rewrite <- Heq.
        apply NoDup_cons; assumption.
      * exact Hnd.
    + unfold ids_of. simpl.
      inversion Hnd. subst.
      apply NoDup_cons.
      * intro Hin. apply H1.
        unfold ids_of in IH.
        rewrite replace_or_add_ids in Hin.
        destruct (existsb (fun x => key_eqb (ev_id x) (ev_id e)) t).
        -- exact Hin.
        -- apply in_app_or in Hin. destruct Hin as [Hin | Hin].
           ++ exact Hin.
           ++ simpl in Hin. destruct Hin as [Hin | []].
              apply key_eqb_neq in Heq. exfalso. apply Heq. symmetry. exact Hin.
      * apply IH. exact H2.
Defined.

Lemma NoDup_filter
  : forall {A} (f : A -> bool) l, NoDup l -> NoDup (filter f l).
Proof.
  intros A f l Hnd. induction l as [| h t IH]; simpl.
  - apply NoDup_nil.
  - inversion Hnd; subst. destruct (f h).
    + apply NoDup_cons.
      * intro Hin. apply H1. apply filter_In in Hin. destruct Hin. exact H.
      * apply IH. exact H2.
    + apply IH. exact H2.
Defined.

Lemma filter_ids_comm
  : forall id l,
    ids_of (filter (fun x => negb (key_eqb (ev_id x) id)) l) =
    filter (fun x => negb (key_eqb x id)) (ids_of l).
Proof.
  intros id l. unfold ids_of.
  induction l as [| a t IH]; simpl.
  - reflexivity.
  - destruct (negb (key_eqb (ev_id a) id)) eqn:Hf; simpl; rewrite IH; reflexivity.
Defined.

Lemma apply_events_NoDup
  : forall stream acc, NoDup (ids_of acc) -> NoDup (ids_of (apply_events stream acc)).
Proof.
  intros stream. induction stream as [| e rest IH]; simpl; intros acc Hnd.
  - exact Hnd.
  - destruct (ev_kind e); apply IH.
    + apply NoDup_replace_or_add. exact Hnd.
    + apply NoDup_replace_or_add. exact Hnd.
    + unfold ids_of. apply cancel_handler_NoDup. exact Hnd.
Defined.

(** * apply_events on a no-cancel, unique-id stream starting from empty. *)

Lemma apply_events_no_cancel_acc
  : forall stream acc,
    no_cancels stream ->
    NoDup (ids_of stream) ->
    (forall e, In e stream -> ~ In (ev_id e) (ids_of acc)) ->
    apply_events stream acc = acc ++ stream.
Proof.
  intros stream. induction stream as [| e rest IH]; simpl; intros acc Hnc Hnd Hfresh.
  - rewrite app_nil_r. reflexivity.
  - assert (Hek : ev_kind e <> Cancel) by (apply Hnc; left; reflexivity).
    destruct (ev_kind e) eqn:Hk; try (exfalso; apply Hek; reflexivity).
    + rewrite replace_or_add_on_fresh_id by (apply Hfresh; left; reflexivity).
      rewrite IH.
      * rewrite <- app_assoc. reflexivity.
      * intros x Hx. apply Hnc. right. exact Hx.
      * inversion Hnd. exact H2.
      * intros x Hx Hin.
        unfold ids_of in Hin. rewrite map_app in Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin].
        -- apply (Hfresh x). right. exact Hx. exact Hin.
        -- simpl in Hin. destruct Hin as [Hin | []].
           inversion Hnd. apply H1.
           unfold ids_of. rewrite Hin. apply in_map. exact Hx.
    + rewrite replace_or_add_on_fresh_id by (apply Hfresh; left; reflexivity).
      rewrite IH.
      * rewrite <- app_assoc. reflexivity.
      * intros x Hx. apply Hnc. right. exact Hx.
      * inversion Hnd. exact H2.
      * intros x Hx Hin.
        unfold ids_of in Hin. rewrite map_app in Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin].
        -- apply (Hfresh x). right. exact Hx. exact Hin.
        -- simpl in Hin. destruct Hin as [Hin | []].
           inversion Hnd. apply H1.
           unfold ids_of. rewrite Hin. apply in_map. exact Hx.
Defined.

(** * Properties preserved through permutation (sort). *)

Lemma no_cancels_perm
  : forall l1 l2, Permutation l1 l2 -> no_cancels l1 -> no_cancels l2.
Proof.
  intros l1 l2 Hp Hnc e Hin.
  apply Hnc. apply (Permutation_in e (Permutation_sym Hp)). exact Hin.
Defined.

Lemma NoDup_ids_perm
  : forall l1 l2, Permutation l1 l2 -> NoDup (ids_of l1) -> NoDup (ids_of l2).
Proof.
  intros l1 l2 Hp Hnd.
  apply Permutation_NoDup with (ids_of l1).
  - unfold ids_of. apply Permutation_map. exact Hp.
  - exact Hnd.
Defined.

(** * Idempotence: canonicalize (canonicalize x) = canonicalize x. *)

Lemma canonicalize_no_cancels
  : forall stream, no_cancels (canonicalize stream).
Proof.
  intro stream. unfold canonicalize.
  apply no_cancels_perm with (apply_events (sort_events stream) []).
  - apply sort_events_perm.
  - apply apply_events_no_cancels. intros x [].
Defined.

Lemma canonicalize_NoDup
  : forall stream, NoDup (ids_of (canonicalize stream)).
Proof.
  intro stream. unfold canonicalize.
  apply NoDup_ids_perm with (apply_events (sort_events stream) []).
  - apply sort_events_perm.
  - apply apply_events_NoDup. apply NoDup_nil.
Defined.

Lemma canonicalize_sorted
  : forall stream, Sorted_leb (canonicalize stream).
Proof.
  intro stream. unfold canonicalize. apply sort_events_sorted.
Defined.

Theorem canonicalize_idempotent
  : forall stream, canonicalize (canonicalize stream) = canonicalize stream.
Proof.
  intro stream.
  set (c := canonicalize stream).
  unfold canonicalize at 1.
  rewrite (sort_sorted_id c (canonicalize_sorted stream)).
  rewrite apply_events_no_cancel_acc.
  - apply sort_sorted_id. apply canonicalize_sorted.
  - apply canonicalize_no_cancels.
  - apply canonicalize_NoDup.
  - intros e _ Hin. destruct Hin.
Defined.

(** * Output ids are a subset of input ids. *)

Lemma replace_or_add_ids_incl
  : forall e acc,
    incl (ids_of (replace_or_add e acc)) (ev_id e :: ids_of acc).
Proof.
  intros e acc. induction acc as [| h t IH]; simpl.
  - intros x [Hx | []]. left. exact Hx.
  - destruct (key_eqb (ev_id h) (ev_id e)) eqn:Heq.
    + destruct (should_replace h e).
      * intros x [Hx | Hx].
        -- left. exact Hx.
        -- right. right. exact Hx.
      * intros x [Hx | Hx].
        -- right. left. exact Hx.
        -- right. right. exact Hx.
    + intros x [Hx | Hx].
      * right. left. exact Hx.
      * destruct (IH x Hx) as [Hy | Hy].
        -- left. exact Hy.
        -- right. right. exact Hy.
Defined.

Lemma filter_ids_incl
  : forall f acc, incl (ids_of (filter f acc)) (ids_of acc).
Proof.
  intros f acc. induction acc as [| h t IH]; simpl.
  - intros x [].
  - destruct (f h).
    + intros x [Hx | Hx].
      * left. exact Hx.
      * right. apply IH. exact Hx.
    + intros x Hx. right. apply IH. exact Hx.
Defined.

Lemma apply_events_ids_incl
  : forall stream acc,
    incl (ids_of (apply_events stream acc))
         (ids_of stream ++ ids_of acc).
Proof.
  intros stream. induction stream as [| e rest IH]; simpl; intros acc.
  - intros x Hx. exact Hx.
  - assert (Hgoal : forall x,
      In x (ids_of (apply_events rest (replace_or_add e acc))) ->
      In x (ev_id e :: ids_of rest ++ ids_of acc)).
    { intros y Hy.
      specialize (IH _ y Hy).
      apply in_app_or in IH. destruct IH as [Hy' | Hy'].
      - right. apply in_or_app. left. exact Hy'.
      - destruct (replace_or_add_ids_incl e acc y Hy') as [Hz | Hz].
        + left. exact Hz.
        + right. apply in_or_app. right. exact Hz. }
    assert (Hgoal2 : forall x,
      In x (ids_of (apply_events rest (cancel_handler e acc))) ->
      In x (ev_id e :: ids_of rest ++ ids_of acc)).
    { intros y Hy.
      specialize (IH _ y Hy).
      apply in_app_or in IH. destruct IH as [Hy' | Hy'].
      - right. apply in_or_app. left. exact Hy'.
      - right. apply in_or_app. right.
        apply (cancel_handler_ids_incl e acc y Hy'). }
    destruct (ev_kind e); intros x Hx.
    + apply Hgoal. exact Hx.
    + apply Hgoal. exact Hx.
    + apply Hgoal2. exact Hx.
Defined.

Lemma ids_of_sort_perm
  : forall l, Permutation (ids_of (sort_events l)) (ids_of l).
Proof.
  intro l. unfold ids_of.
  apply Permutation_map. apply Permutation_sym. apply sort_events_perm.
Defined.

Theorem canonicalize_ids_subset
  : forall stream,
    incl (ids_of (canonicalize stream)) (ids_of stream).
Proof.
  intro stream. unfold canonicalize.
  intros x Hx.
  set (ae := apply_events (sort_events stream) []) in *.
  assert (Hin : In x (ids_of ae)).
  { apply (Permutation_in x (ids_of_sort_perm ae)). exact Hx. }
  assert (Hin2 : In x (ids_of (sort_events stream) ++ ids_of [])).
  { apply (apply_events_ids_incl (sort_events stream) [] x Hin). }
  simpl in Hin2. rewrite app_nil_r in Hin2.
  apply (Permutation_in x (ids_of_sort_perm stream)). exact Hin2.
Defined.

(** * Semantic characterization of canonicalize.
    An id appears in the output iff the last event for that id
    (in sort order) is not a Cancel. This is the spec-level theorem
    that says what canonicalize computes, not just its algebraic properties. *)

Lemma replace_or_add_has_id
  : forall e acc, In (ev_id e) (ids_of (replace_or_add e acc)).
Proof.
  intros e acc. induction acc as [| h t IH]; simpl.
  - left. reflexivity.
  - destruct (key_eqb (ev_id h) (ev_id e)) eqn:Heq.
    + destruct (should_replace h e).
      * left. reflexivity.
      * left. apply key_eqb_eq. exact Heq.
    + right. exact IH.
Defined.

Lemma replace_or_add_other_id
  : forall e acc id,
    ev_id e <> id ->
    In id (ids_of (replace_or_add e acc)) <-> In id (ids_of acc).
Proof.
  intros e acc id Hne. induction acc as [| h t IH]; simpl.
  - split.
    + intros [Hx | []]. exfalso. apply Hne. exact Hx.
    + intros [].
  - destruct (key_eqb (ev_id h) (ev_id e)) eqn:Heq.
    + destruct (should_replace h e).
      * apply key_eqb_eq in Heq.
        unfold ids_of. simpl. rewrite Heq.
        split; intro H; exact H.
      * split; intro H; exact H.
    + simpl. split.
      * intros [Hx | Hx]; [ left; exact Hx | right; apply IH; exact Hx ].
      * intros [Hx | Hx]; [ left; exact Hx | right; apply IH; exact Hx ].
Defined.

Lemma filter_removes_id
  : forall id acc,
    ~ In id (ids_of (filter (fun x => negb (key_eqb (ev_id x) id)) acc)).
Proof.
  intros id acc. induction acc as [| h t IH]; simpl.
  - intro H. exact H.
  - destruct (negb (key_eqb (ev_id h) id)) eqn:Hf.
    + simpl. intros [Hx | Hx].
      * apply negb_true_iff in Hf. apply key_eqb_neq in Hf.
        apply Hf. exact Hx.
      * exact (IH Hx).
    + exact IH.
Defined.

Lemma filter_preserves_other_id
  : forall id id' acc,
    id' <> id ->
    In id' (ids_of (filter (fun x => negb (key_eqb (ev_id x) id)) acc)) <->
    In id' (ids_of acc).
Proof.
  intros id id' acc Hne. induction acc as [| h t IH]; simpl.
  - split; intro H; exact H.
  - destruct (negb (key_eqb (ev_id h) id)) eqn:Hf.
    + simpl. split.
      * intros [Hx | Hx]; [ left; exact Hx | right; apply IH; exact Hx ].
      * intros [Hx | Hx]; [ left; exact Hx | right; apply IH; exact Hx ].
    + split.
      * intro Hx. right. apply IH. exact Hx.
      * intros [Hx | Hx].
        -- exfalso. apply negb_false_iff in Hf. apply key_eqb_eq in Hf.
           apply Hne. rewrite <- Hx. exact Hf.
        -- apply IH. exact Hx.
Defined.

(** Helper: if no event in the stream has id, the acc is transparent. *)

Lemma apply_events_no_id_transparent
  : forall stream acc id,
    (forall e, In e stream -> ev_id e <> id) ->
    In id (ids_of (apply_events stream acc)) <-> In id (ids_of acc).
Proof.
  induction stream as [| e rest IH]; simpl; intros acc id Hall.
  - split; intro H; exact H.
  - assert (Hne : ev_id e <> id) by (apply Hall; left; reflexivity).
    assert (Hrest : forall x, In x rest -> ev_id x <> id)
      by (intros x Hx; apply Hall; right; exact Hx).
    destruct (ev_kind e) eqn:Hk.
    + rewrite IH by exact Hrest.
      apply replace_or_add_other_id. exact Hne.
    + rewrite IH by exact Hrest.
      apply replace_or_add_other_id. exact Hne.
    + rewrite IH by exact Hrest.
      unfold ids_of. apply cancel_handler_preserves_other_id. exact Hne.
Defined.

Theorem apply_events_spec
  : forall stream acc id,
    In id (ids_of (apply_events stream acc)) <->
    match last_with_id id stream with
    | None => In id (ids_of acc)
    | Some e => ev_kind e <> Cancel
    end.
Proof.
  induction stream as [| e rest IH]; simpl; intros acc id.
  - split; intro H; exact H.
  - destruct (last_with_id id rest) eqn:Hlast.
    + (* Last event for id is in rest — head doesn't change the answer. *)
      destruct (ev_kind e) eqn:Hk.
      * specialize (IH (replace_or_add e acc) id). rewrite Hlast in IH. exact IH.
      * specialize (IH (replace_or_add e acc) id). rewrite Hlast in IH. exact IH.
      * specialize (IH (cancel_handler e acc) id).
        rewrite Hlast in IH. exact IH.
    + (* No event for id in rest. *)
      assert (Hrest : forall x, In x rest -> ev_id x <> id)
        by (intros x Hx; exact (last_with_id_None id rest Hlast x Hx)).
      destruct (key_eqb (ev_id e) id) eqn:Heq.
      * apply key_eqb_eq in Heq. subst id.
        destruct (ev_kind e) eqn:Hk.
        -- (* Original: adds to acc, rest doesn't touch it. *)
           rewrite apply_events_no_id_transparent by exact Hrest.
           split.
           ++ intro. discriminate.
           ++ intro. apply replace_or_add_has_id.
        -- (* Correction: same. *)
           rewrite apply_events_no_id_transparent by exact Hrest.
           split.
           ++ intro. discriminate.
           ++ intro. apply replace_or_add_has_id.
        -- (* Cancel: removes from acc, rest doesn't re-add. *)
           rewrite apply_events_no_id_transparent by exact Hrest.
           split.
           ++ intro Hin. exfalso. exact (cancel_handler_removes_id e acc Hin).
           ++ intro Habs. exfalso. apply Habs. reflexivity.
      * (* Head event has different id — transparent. *)
        apply key_eqb_neq in Heq.
        destruct (ev_kind e) eqn:Hk.
        -- rewrite apply_events_no_id_transparent by exact Hrest.
           apply replace_or_add_other_id. exact Heq.
        -- rewrite apply_events_no_id_transparent by exact Hrest.
           apply replace_or_add_other_id. exact Heq.
        -- rewrite apply_events_no_id_transparent by exact Hrest.
           unfold ids_of. apply cancel_handler_preserves_other_id. exact Heq.
Defined.

(** Lift to canonicalize. *)

Theorem canonicalize_spec
  : forall stream id,
    In id (ids_of (canonicalize stream)) <->
    match last_with_id id (sort_events stream) with
    | None => False
    | Some e => ev_kind e <> Cancel
    end.
Proof.
  intros stream id. unfold canonicalize.
  rewrite <- (apply_events_spec (sort_events stream) [] id).
  split.
  - intro Hx. apply (Permutation_in id (ids_of_sort_perm _)) in Hx.
    exact Hx.
  - intro Hx. apply (Permutation_in id (Permutation_sym (ids_of_sort_perm _))).
    exact Hx.
Defined.

(** * Online processing via fold_left. *)

Definition process_one (acc : list event) (e : event) : list event :=
  match ev_kind e with
  | Original => replace_or_add e acc
  | Correction => replace_or_add e acc
  | Cancel => cancel_handler e acc
  end.

Lemma fold_left_eq_apply_events
  : forall stream acc,
    fold_left process_one stream acc = apply_events stream acc.
Proof.
  induction stream as [| e rest IH]; intro acc.
  - reflexivity.
  - simpl. rewrite IH. unfold process_one.
    destruct (ev_kind e); reflexivity.
Defined.

(** Online-batch equivalence: processing any sorted stream incrementally
    via fold_left, then sorting the result, equals canonicalize. This is
    non-trivial because fold_left operates left-to-right on a pre-sorted
    stream, while canonicalize composes sort-apply-sort. The equivalence
    follows from fold_left = apply_events and the definition of canonicalize. *)

Definition fold_stream (stream : list event) : list event :=
  sort_events (fold_left process_one (sort_events stream) []).

Theorem online_batch_equiv
  : forall stream, fold_stream stream = canonicalize stream.
Proof.
  intro stream. unfold fold_stream, canonicalize.
  rewrite fold_left_eq_apply_events. reflexivity.
Defined.

(** Stronger form: for any partitioning of a sorted stream into contiguous
    chunks, processing each chunk sequentially equals batch processing. *)

Theorem chunked_processing
  : forall chunks acc,
    fold_left (fun a chunk => apply_events chunk a) chunks acc =
    apply_events (concat chunks) acc.
Proof.
  induction chunks as [| c rest IH]; simpl; intro acc.
  - reflexivity.
  - rewrite IH. rewrite apply_events_app. reflexivity.
Defined.

(** * Gap detection: find event ids present in the stream but absent
    from the canonical output, indicating they were cancelled or
    superseded without replacement. *)

Fixpoint mem_key (n : Key) (l : list Key) : bool :=
  match l with
  | [] => false
  | h :: t => key_eqb n h || mem_key n t
  end.

Fixpoint dedup_key (l : list Key) : list Key :=
  match l with
  | [] => []
  | h :: t =>
    if mem_key h t then dedup_key t
    else h :: dedup_key t
  end.

Definition detect_gaps (stream : list event) : list Key :=
  let input_ids := dedup_key (ids_of stream) in
  let output_ids := ids_of (canonicalize stream) in
  filter (fun id => negb (mem_key id output_ids)) input_ids.

End Parameterized.

(** * Nat-payload instantiation for worked examples and extraction. *)

Definition nat_payload_compare := Nat.compare.
Definition nat_payload_eqb := Nat.eqb.

Lemma nat_payload_compare_refl : forall p, Nat.compare p p = Eq.
Proof. intro. apply Nat.compare_refl. Qed.

Lemma nat_payload_compare_antisym
  : forall p1 p2, Nat.compare p1 p2 = CompOpp (Nat.compare p2 p1).
Proof. intros. apply Nat.compare_antisym. Qed.

Lemma nat_payload_compare_eq
  : forall p1 p2, Nat.compare p1 p2 = Eq -> p1 = p2.
Proof. intros. apply Nat.compare_eq_iff. exact H. Qed.

Lemma nat_payload_compare_not_gt_trans
  : forall p1 p2 p3,
    Nat.compare p1 p2 <> Gt ->
    Nat.compare p2 p3 <> Gt ->
    Nat.compare p1 p3 <> Gt.
Proof.
  intros p1 p2 p3 H1 H2 H3.
  destruct (Nat.compare p1 p2) eqn:E1; [ | | exfalso; apply H1; reflexivity ].
  - apply Nat.compare_eq_iff in E1. subst p2. apply H2. exact H3.
  - destruct (Nat.compare p2 p3) eqn:E2; [ | | exfalso; apply H2; reflexivity ].
    + apply Nat.compare_eq_iff in E2. subst p3. rewrite E1 in H3. discriminate.
    + rewrite Nat.compare_lt_iff in E1.
      rewrite Nat.compare_lt_iff in E2.
      rewrite Nat.compare_gt_iff in H3.
      lia.
Qed.

Lemma nat_payload_eqb_spec
  : forall p1 p2, reflect (p1 = p2) (Nat.eqb p1 p2).
Proof. intros. apply Nat.eqb_spec. Qed.

Definition nat_should_replace (old new_ : event nat nat) : bool :=
  Nat.leb (ev_seq nat nat old) (ev_seq nat nat new_).

Definition nat_cancel_handler (e : event nat nat) (acc : list (event nat nat))
  : list (event nat nat) :=
  filter (fun x => negb (Nat.eqb (ev_id nat nat x) (ev_id nat nat e))) acc.

(** * Discharge cancel_handler hypotheses for nat_cancel_handler. *)

Lemma nat_cancel_handler_removes_id
  : forall e acc, ~ In (ev_id nat nat e) (map (ev_id nat nat) (nat_cancel_handler e acc)).
Proof.
  intros e acc. unfold nat_cancel_handler.
  induction acc as [| h t IH]; simpl.
  - intro H. exact H.
  - destruct (negb (Nat.eqb (ev_id nat nat h) (ev_id nat nat e))) eqn:Hf.
    + simpl. intros [Hx | Hx].
      * apply negb_true_iff in Hf. apply Nat.eqb_neq in Hf.
        apply Hf. exact Hx.
      * exact (IH Hx).
    + exact IH.
Qed.

Lemma nat_cancel_handler_preserves_other_id
  : forall e acc id,
    ev_id nat nat e <> id ->
    In id (map (ev_id nat nat) (nat_cancel_handler e acc)) <-> In id (map (ev_id nat nat) acc).
Proof.
  intros e acc id Hne. unfold nat_cancel_handler.
  induction acc as [| h t IH]; simpl.
  - split; intro H; exact H.
  - destruct (negb (Nat.eqb (ev_id nat nat h) (ev_id nat nat e))) eqn:Hf.
    + simpl. split.
      * intros [Hx | Hx]; [ left; exact Hx | right; apply IH; exact Hx ].
      * intros [Hx | Hx]; [ left; exact Hx | right; apply IH; exact Hx ].
    + apply negb_false_iff in Hf. apply Nat.eqb_eq in Hf.
      split.
      * intro Hx. right. apply IH. exact Hx.
      * intros [Hx | Hx].
        -- exfalso. apply Hne. rewrite <- Hx. symmetry. exact Hf.
        -- apply IH. exact Hx.
Qed.

Lemma nat_cancel_handler_no_cancels
  : forall e acc,
    (forall x, In x acc -> ev_kind nat nat x <> Cancel) ->
    (forall x, In x (nat_cancel_handler e acc) -> ev_kind nat nat x <> Cancel).
Proof.
  intros e acc Hacc x Hx. unfold nat_cancel_handler in Hx.
  apply filter_In in Hx. destruct Hx as [Hin _].
  apply Hacc. exact Hin.
Qed.

Lemma nat_cancel_handler_NoDup
  : forall e acc,
    NoDup (map (ev_id nat nat) acc) ->
    NoDup (map (ev_id nat nat) (nat_cancel_handler e acc)).
Proof.
  intros e acc Hnd. unfold nat_cancel_handler.
  induction acc as [| h t IH]; simpl.
  - apply NoDup_nil.
  - inversion Hnd; subst.
    destruct (negb (Nat.eqb (ev_id nat nat h) (ev_id nat nat e))) eqn:Hf.
    + simpl. apply NoDup_cons.
      * intro Hin. apply H1.
        clear -Hin. induction t as [| a t' IHt]; simpl in *.
        -- exact Hin.
        -- destruct (negb (Nat.eqb (ev_id nat nat a) (ev_id nat nat e))).
           ++ simpl in Hin. destruct Hin as [Hx | Hx].
              ** left. exact Hx.
              ** right. apply IHt. exact Hx.
           ++ right. apply IHt. exact Hin.
      * apply IH. exact H2.
    + apply IH. exact H2.
Qed.

Lemma nat_cancel_handler_ids_incl
  : forall e acc,
    incl (map (ev_id nat nat) (nat_cancel_handler e acc)) (map (ev_id nat nat) acc).
Proof.
  intros e acc. unfold nat_cancel_handler.
  intros x Hx.
  induction acc as [| h t IH]; simpl in *.
  - exact Hx.
  - destruct (negb (Nat.eqb (ev_id nat nat h) (ev_id nat nat e))) eqn:Hf.
    + simpl in Hx. destruct Hx as [Hx | Hx].
      * left. exact Hx.
      * right. apply IH. exact Hx.
    + right. apply IH. exact Hx.
Qed.

Lemma nat_cancel_handler_preserves_event
  : forall e acc x,
    ev_id nat nat e <> ev_id nat nat x ->
    In x (nat_cancel_handler e acc) <-> In x acc.
Proof.
  intros e acc x Hne. unfold nat_cancel_handler.
  induction acc as [| h t IH]; simpl.
  - split; intro H; exact H.
  - destruct (negb (Nat.eqb (ev_id nat nat h) (ev_id nat nat e))) eqn:Hf.
    + simpl. split.
      * intros [Hx | Hx]; [ left; exact Hx | right; apply IH; exact Hx ].
      * intros [Hx | Hx]; [ left; exact Hx | right; apply IH; exact Hx ].
    + apply negb_false_iff in Hf. apply Nat.eqb_eq in Hf.
      split.
      * intro Hx. right. apply IH. exact Hx.
      * intros [Hx | Hx].
        -- exfalso. subst h. apply Hne. symmetry. exact Hf.
        -- apply IH. exact Hx.
Qed.

(** * Discharge kmap hypotheses for IdMap (FMapAVL over Nat_as_OT). *)

Definition nat_kmap := IdMap.t (event nat nat).
Definition nat_kmap_find := @IdMap.find (event nat nat).
Definition nat_kmap_add := @IdMap.add (event nat nat).
Definition nat_kmap_remove := @IdMap.remove (event nat nat).
Definition nat_kmap_In (k : nat) (m : nat_kmap) : Prop := IdMap.In k m.
Definition nat_kmap_elements := @IdMap.elements (event nat nat).
Definition nat_kmap_empty := @IdMap.empty (event nat nat).

Lemma nat_kmap_find_In
  : forall k m v, nat_kmap_find k m = Some v -> nat_kmap_In k m.
Proof.
  intros k m v H. unfold nat_kmap_find, nat_kmap_In.
  exists v. apply IdMap.find_2. exact H.
Qed.

Lemma nat_kmap_add_In_same
  : forall k v m, nat_kmap_In k (nat_kmap_add k v m).
Proof.
  intros k v m. unfold nat_kmap_In, nat_kmap_add.
  exists v. apply IdMap.add_1. reflexivity.
Qed.

Lemma nat_kmap_add_In_other
  : forall k k' v m, k <> k' -> (nat_kmap_In k' (nat_kmap_add k v m) <-> nat_kmap_In k' m).
Proof.
  intros k k' v m Hne. unfold nat_kmap_In, nat_kmap_add. split.
  - intros [v' Hm]. exists v'.
    apply IdMap.add_3 with k v; [ | exact Hm ].
    intro Heq. apply Hne. exact Heq.
  - intros [v' Hm]. exists v'.
    apply IdMap.add_2; [ | exact Hm ].
    intro Heq. apply Hne. exact Heq.
Qed.

Lemma nat_kmap_remove_not_In
  : forall k m, ~ nat_kmap_In k (nat_kmap_remove k m).
Proof.
  intros k m. unfold nat_kmap_In, nat_kmap_remove.
  apply IdMap.remove_1. reflexivity.
Qed.

Lemma nat_kmap_remove_In_other
  : forall k k' m, k' <> k -> (nat_kmap_In k' (nat_kmap_remove k m) <-> nat_kmap_In k' m).
Proof.
  intros k k' m Hne. unfold nat_kmap_In, nat_kmap_remove. split.
  - intros [v Hm]. exists v.
    apply IdMap.remove_3 with k. exact Hm.
  - intros [v Hm]. exists v.
    apply IdMap.remove_2; [ | exact Hm ].
    intro Heq. apply Hne. symmetry. exact Heq.
Qed.

Lemma nat_kmap_find_empty
  : forall k, nat_kmap_find k nat_kmap_empty = None.
Proof.
  intro k. unfold nat_kmap_find, nat_kmap_empty.
  destruct (IdMap.find k (IdMap.empty (event nat nat))) eqn:Hf.
  - exfalso. apply IdMap.find_2 in Hf.
    apply (IdMap.empty_1) in Hf. exact Hf.
  - reflexivity.
Qed.

Lemma nat_kmap_find_add_same
  : forall k v m, nat_kmap_find k (nat_kmap_add k v m) = Some v.
Proof.
  intros k v m. unfold nat_kmap_find, nat_kmap_add.
  apply IdMap.find_1. apply IdMap.add_1. reflexivity.
Qed.

Lemma nat_kmap_find_add_other
  : forall k k' v m, k <> k' -> nat_kmap_find k' (nat_kmap_add k v m) = nat_kmap_find k' m.
Proof.
  intros k k' v m Hne. unfold nat_kmap_find, nat_kmap_add.
  destruct (IdMap.find k' m) eqn:Hm.
  - apply IdMap.find_2 in Hm.
    apply IdMap.find_1. apply IdMap.add_2.
    + intro Heq. apply Hne. exact Heq.
    + exact Hm.
  - destruct (IdMap.find k' (IdMap.add k v m)) eqn:Ha.
    + exfalso. apply IdMap.find_2 in Ha.
      apply IdMap.add_3 in Ha; [ | intro Heq; apply Hne; exact Heq ].
      rewrite (IdMap.find_1 Ha) in Hm. discriminate.
    + reflexivity.
Qed.

Lemma nat_kmap_find_remove_same
  : forall k m, nat_kmap_find k (nat_kmap_remove k m) = None.
Proof.
  intros k m. unfold nat_kmap_find, nat_kmap_remove.
  destruct (IdMap.find k (IdMap.remove k m)) eqn:Hr.
  - exfalso. apply IdMap.find_2 in Hr.
    assert (Hin : IdMap.In k (IdMap.remove k m)) by (exists e; exact Hr).
    exact (IdMap.remove_1 (eq_refl k) Hin).
  - reflexivity.
Qed.

Lemma nat_kmap_find_remove_other
  : forall k k' m, k' <> k -> nat_kmap_find k' (nat_kmap_remove k m) = nat_kmap_find k' m.
Proof.
  intros k k' m Hne. unfold nat_kmap_find, nat_kmap_remove.
  destruct (IdMap.find k' m) eqn:Hm.
  - apply IdMap.find_2 in Hm.
    apply IdMap.find_1. apply IdMap.remove_2.
    + intro Heq. apply Hne. symmetry. exact Heq.
    + exact Hm.
  - destruct (IdMap.find k' (IdMap.remove k m)) eqn:Hr.
    + exfalso. apply IdMap.find_2 in Hr.
      apply IdMap.remove_3 in Hr.
      rewrite (IdMap.find_1 Hr) in Hm. discriminate.
    + reflexivity.
Qed.

Lemma nat_kmap_elements_correct
  : forall k v m,
    In (k, v) (nat_kmap_elements m) <-> nat_kmap_find k m = Some v.
Proof.
  intros k v m. unfold nat_kmap_elements, nat_kmap_find. split.
  - intro H. apply IdMap.find_1. apply IdMap.elements_2.
    rewrite InA_alt. exists (k, v). split; [ reflexivity | exact H ].
  - intro H. apply IdMap.find_2 in H. apply IdMap.elements_1 in H.
    rewrite InA_alt in H. destruct H as [[k' v'] [Heq Hin]].
    compute in Heq. destruct Heq as [Hk Hv]. subst k' v'. exact Hin.
Qed.

Lemma NoDupA_eq_key_NoDup_fst
  : forall {A : Type} (l : list (nat * A)),
    NoDupA (@IdMap.eq_key A) l -> NoDup (map fst l).
Proof.
  intros A l H. induction H as [| [k v] l Hni Hnd IH]; simpl.
  - apply NoDup_nil.
  - apply NoDup_cons.
    + intro Hin. apply Hni.
      clear -Hin. induction l as [| [k' v'] t IHl]; simpl in *.
      * destruct Hin.
      * destruct Hin as [Hx | Hx].
        -- left. red. simpl. symmetry. exact Hx.
        -- right. apply IHl. exact Hx.
    + exact IH.
Qed.

Lemma nat_kmap_elements_NoDup
  : forall m, NoDup (map fst (nat_kmap_elements m)).
Proof.
  intro m. unfold nat_kmap_elements.
  apply NoDupA_eq_key_NoDup_fst. apply IdMap.elements_3w.
Qed.

(** Convenience aliases for the nat-instantiated definitions. *)

Notation nat_event := (event nat nat).
Notation nat_canonicalize := (canonicalize nat Nat.compare Nat.eqb nat Nat.compare nat_should_replace nat_cancel_handler).
Notation nat_fold_stream := (fold_stream nat Nat.compare Nat.eqb nat Nat.compare nat_should_replace nat_cancel_handler).
Notation nat_sort_events := (sort_events nat Nat.compare nat Nat.compare).
Notation nat_apply_events := (apply_events nat Nat.eqb nat nat_should_replace nat_cancel_handler).
Notation nat_process_one := (process_one nat Nat.eqb nat nat_should_replace nat_cancel_handler).
Notation nat_event_leb := (event_leb nat Nat.compare nat Nat.compare).
Notation nat_event_eqb := (event_eqb nat Nat.eqb nat Nat.compare Nat.eqb).
Notation nat_detect_gaps := (detect_gaps nat Nat.compare Nat.eqb nat Nat.compare nat_should_replace nat_cancel_handler).
Notation nat_replace_or_add_map := (replace_or_add_map nat Nat.eqb nat nat_should_replace).
Notation nat_apply_events_map := (apply_events_map nat Nat.eqb nat nat_should_replace).
Notation nat_map_values := (map_values nat nat).

(** * Worked examples: real-world canonicalization scenarios.

    All examples use small natural numbers to stay within Coq's unary
    nat representation.  Each scenario documents the real-world encoding:
    what the ids, timestamps, and payloads represent in the domain.
    The canonicalizer is domain-agnostic; the examples exist to show
    that the algebraic properties (determinism, idempotence, no cancel
    leakage, unique ids, online-batch equivalence) hold on realistic
    event topologies — not just unit-test-sized inputs. *)

(** Notational convenience. *)

Definition orig  id ts sq pl := @mkEvent nat nat id ts sq pl Original.
Definition corr  id ts sq pl := @mkEvent nat nat id ts sq pl Correction.
Definition cancl id ts sq    := @mkEvent nat nat id ts sq 0  Cancel.

(** ** I. Equity trading desk — flash-crash replay.

    A burst of executions arrives out of order from three venues
    during a flash crash.  Two fills are amended (price improvement
    from the matching engine), one is busted entirely by the exchange.
    The canonical stream must reconstruct the true position regardless
    of wire ordering.

    Encoding: ids are execution ids (11-15); timestamps are
    microsecond offsets from market open (10-50); payloads encode
    price in hundredths (e.g. 523 = $5.23). *)

Definition flash_crash_raw : list nat_event :=
  [ orig  11 10 0 523    (* AAPL fill 100 @ 5.23, venue A *)
  ; orig  12 20 0 817    (* MSFT fill  50 @ 8.17, venue B *)
  ; orig  13 15 0 519    (* AAPL fill 200 @ 5.19, venue C *)
  ; corr  11 10 1 525    (* venue A amends: price was 5.25 *)
  ; orig  14 30 0 811    (* MSFT fill 100 @ 8.11, venue A *)
  ; cancl 13 15 1        (* venue C busts the 200-lot *)
  ; orig  12 20 0 817    (* duplicate wire — venue B retransmit *)
  ; corr  14 30 1 813    (* venue A amends: price was 8.13 *)
  ; orig  15 50 0 530    (* AAPL fill 300 @ 5.30, venue B *)
  ].

(** After canonicalization the busted fill (13) and the duplicate (12)
    vanish; corrections to 11 and 14 replace the originals; five raw
    executions reduce to four priced fills in strict time order. *)

Eval compute in (nat_canonicalize flash_crash_raw).

Eval compute in (nat_detect_gaps flash_crash_raw).
(* = [13]  — the busted fill. *)

(** Idempotence: the desk can safely re-ingest its own output. *)

Example flash_crash_idempotent
  : nat_canonicalize (nat_canonicalize flash_crash_raw) = nat_canonicalize flash_crash_raw.
Proof. native_compute. reflexivity. Qed.

(** ** II. IoT sensor mesh — industrial cooling loop.

    Four temperature sensors report every 5 seconds.  Sensor 42
    drifts and sends a correction; sensor 43 is decommissioned
    mid-window and its readings are cancelled; sensor 41 transmits
    a stale duplicate over a flaky LoRa link.

    Encoding: ids are sensor ids (41-44); timestamps are seconds
    within the window (100, 105); payloads are decidegrees Celsius
    (372 = 37.2 C). *)

Definition cooling_loop_raw : list nat_event :=
  [ orig  41 100 0 372    (* sensor 41: 37.2 C *)
  ; orig  42 100 0 384    (* sensor 42: 38.4 C *)
  ; orig  43 100 0 291    (* sensor 43: 29.1 C *)
  ; orig  44 100 0 310    (* sensor 44: 31.0 C *)
  ; orig  41 105 1 373    (* sensor 41: 37.3 C, next cycle *)
  ; corr  42 100 1 381    (* sensor 42 recalibrates: was 38.1 C *)
  ; orig  41 100 0 372    (* stale retransmit from sensor 41 *)
  ; cancl 43 100 1        (* sensor 43 decommissioned *)
  ; orig  42 105 2 382    (* sensor 42: 38.2 C, next cycle *)
  ; orig  44 105 1 311    (* sensor 44: 31.1 C, next cycle *)
  ].

(** Canonical telemetry: sensor 43 vanishes, sensor 42's first
    reading is corrected, stale retransmit from 41 is absorbed. *)

Eval compute in (nat_canonicalize cooling_loop_raw).

Eval compute in (nat_detect_gaps cooling_loop_raw).
(* = [43]  — the decommissioned sensor. *)

Example cooling_loop_deterministic :
  let reversed := rev cooling_loop_raw in
  nat_canonicalize reversed = nat_canonicalize cooling_loop_raw.
Proof. native_compute. reflexivity. Qed.

(** ** III. Regulatory trade reporting — MiFID II amendment chain.

    A broker reports five trades to the ARM (Approved Reporting
    Mechanism).  Two are amended for price; one is cancelled as
    erroneous; a fourth is amended twice in succession (only the
    latest amendment survives).  The regulator replays the feed
    and must recover the identical golden record regardless of
    message ordering or duplication.

    Encoding: ids are trade report ids (51-55); timestamps are
    seconds since midnight (200-204); payloads are notional in
    cents (e.g. 950 = $9.50). *)

Definition mifid_raw : list nat_event :=
  [ orig  51 200 0 950    (* trade A: notional 9.50 *)
  ; orig  52 201 0 525    (* trade B: notional 5.25 *)
  ; orig  53 202 0 750    (* trade C: notional 7.50 *)
  ; orig  54 203 0 120    (* trade D: notional 1.20 *)
  ; orig  55 204 0 300    (* trade E: notional 3.00 *)
  ; corr  51 200 1 975    (* amend A: notional 9.75 *)
  ; cancl 53 202 1        (* cancel C: erroneous *)
  ; corr  54 203 1 195    (* amend D first: 1.95 *)
  ; corr  54 203 2 198    (* amend D second: 1.98 *)
  ; orig  52 201 0 525    (* duplicate B from backup feed *)
  ; corr  51 200 1 975    (* duplicate amendment A *)
  ].

Eval compute in (nat_canonicalize mifid_raw).
(* Four trades survive: 51 (amended), 52, 54 (second amend wins), 55.
   Trade 53 is cancelled. *)

Eval compute in (nat_detect_gaps mifid_raw).
(* = [53]  — the erroneous trade. *)

(** The regulator re-ingests the golden record; nothing changes. *)

Example mifid_idempotent
  : nat_canonicalize (nat_canonicalize mifid_raw) = nat_canonicalize mifid_raw.
Proof. native_compute. reflexivity. Qed.

(** ** IV. Distributed event sourcing — order lifecycle.

    An e-commerce system models each order as a stream of domain
    events.  Microservices emit events independently; network
    partitions cause duplicates and reordering.  The read-side
    projection must converge to a single truth.

    Encoding: ids are order-event ids (61-68); timestamps are
    logical clock ticks (10-80); payloads encode price in cents
    where relevant (499 = $4.99). *)

Definition order_lifecycle_raw : list nat_event :=
  [ orig  61 10 0 499    (* order placed: $4.99 *)
  ; orig  62 11 0 0      (* payment authorized *)
  ; orig  63 12 0 499    (* inventory reserved *)
  ; corr  61 10 1 449    (* price adjustment: $4.49, coupon applied *)
  ; orig  64 13 0 0      (* shipment label created *)
  ; cancl 63 12 1        (* inventory reservation released — out of stock *)
  ; orig  65 14 0 0      (* backorder placed *)
  ; orig  63 12 0 499    (* stale retry from inventory service *)
  ; orig  66 20 0 449    (* inventory re-reserved at new price *)
  ; corr  64 13 1 0      (* shipment label regenerated for new warehouse *)
  ; orig  62 11 0 0      (* duplicate payment auth from retry queue *)
  ; orig  67 21 0 0      (* shipped *)
  ; orig  68 30 0 0      (* delivered *)
  ].

Eval compute in (nat_canonicalize order_lifecycle_raw).
(* Full lifecycle minus the released reservation, deduped,
   with the coupon price and regenerated label. *)

Eval compute in (nat_detect_gaps order_lifecycle_raw).
(* = [63]  — the released inventory hold. *)

Example order_lifecycle_online_batch :
  nat_fold_stream order_lifecycle_raw = nat_canonicalize order_lifecycle_raw.
Proof. native_compute. reflexivity. Qed.

(** ** V. High-frequency market data — depth-of-book reconstruction.

    A consolidated feed carries order-book updates from two exchanges
    (odd ids = exchange A, even ids = exchange B).  Orders are placed,
    amended, and cancelled in rapid succession.  The canonical book
    is the input to a fair-value model that must be deterministic
    across replays regardless of interleaving.

    Encoding: ids are order ids (1-9); timestamps are nanosecond
    offsets (1-11); payloads encode price in hundredths
    (e.g. 525 = $5.25). *)

Definition orderbook_raw : list nat_event :=
  [ orig  1 1 0 525     (* A: bid 5.25 *)
  ; orig  2 2 0 530     (* B: ask 5.30 *)
  ; orig  3 3 0 520     (* A: bid 5.20 *)
  ; orig  4 4 0 535     (* B: ask 5.35 *)
  ; corr  1 1 1 526     (* A amends bid to 5.26 *)
  ; orig  5 6 0 518     (* A: bid 5.18 *)
  ; cancl 3 3 1         (* A pulls bid 5.20 *)
  ; orig  6 7 0 532     (* B: ask 5.32 *)
  ; cancl 4 4 1         (* B pulls ask 5.35 *)
  ; corr  2 2 1 529     (* B tightens ask to 5.29 *)
  ; orig  7 9 0 527     (* A: bid 5.27 *)
  ; cancl 6 7 1         (* B pulls ask 5.32 *)
  ; orig  8 10 0 528    (* B: ask 5.28 — crosses with 7! *)
  ; orig  2 2 0 530     (* stale retransmit from B *)
  ; orig  9 11 0 527    (* A: new bid 5.27 — replenish *)
  ].

Eval compute in (nat_canonicalize orderbook_raw).
(* Surviving resting orders: 1 (amended), 2 (tightened),
   5, 7, 8, 9.  Pulled orders 3, 4, 6 vanish. *)

Eval compute in (nat_detect_gaps orderbook_raw).
(* = [3; 4; 6]  — the three pulled orders. *)

(** Shuffling the consolidated tape must produce the same book. *)

Example orderbook_deterministic :
  let alt_order :=
    [ orig  8 10 0 528
    ; cancl 4 4 1
    ; orig  5 6 0 518
    ; orig  2 2 0 530
    ; cancl 6 7 1
    ; orig  1 1 0 525
    ; corr  2 2 1 529
    ; orig  7 9 0 527
    ; orig  3 3 0 520
    ; cancl 3 3 1
    ; corr  1 1 1 526
    ; orig  4 4 0 535
    ; orig  6 7 0 532
    ; orig  9 11 0 527
    ; orig  2 2 0 530
    ] in
  nat_canonicalize alt_order = nat_canonicalize orderbook_raw.
Proof. native_compute. reflexivity. Qed.

(** ** VI. Clinical trial data — adverse event reconciliation.

    A multi-site pharmaceutical trial collects adverse-event reports.
    Sites submit, amend, and retract reports; the sponsor must produce
    a single reconciled safety database for regulatory submission.

    Encoding: ids are report ids (31-37); timestamps are study
    day numbers (1-7); payloads encode MedDRA preferred-term codes
    truncated to last three digits (e.g. 211 for PT 10019211). *)

Definition clinical_raw : list nat_event :=
  [ orig  31 1 0 100    (* site 1: headache, PT ...100 *)
  ; orig  32 2 0 813    (* site 2: nausea, PT ...813 *)
  ; orig  33 3 0 700    (* site 3: vomiting, PT ...700 *)
  ; orig  34 4 0 378    (* site 1: diarrhea, PT ...378 *)
  ; corr  31 1 1 211    (* site 1 recodes: migraine, PT ...211 *)
  ; orig  35 5 0 844    (* site 2: rash, PT ...844 *)
  ; cancl 33 3 1        (* site 3 retracts: was pre-existing *)
  ; orig  33 3 0 700    (* stale retransmit from site 3 EDC *)
  ; corr  32 2 1 836    (* site 2 recodes: nausea aggravated *)
  ; orig  36 6 0 199    (* site 1: anaphylaxis — serious AE *)
  ; corr  31 1 2 211    (* duplicate correction from audit *)
  ; orig  37 7 0 558    (* site 3: fatigue, PT ...558 *)
  ].

Eval compute in (nat_canonicalize clinical_raw).
(* Six reports survive: 31 (recoded to migraine), 32 (recoded),
   34 (diarrhea), 35 (rash), 36 (anaphylaxis), 37 (fatigue).
   Report 33 (pre-existing vomiting) is retracted. *)

Eval compute in (nat_detect_gaps clinical_raw).
(* = [33]  — the retracted report. *)

Example clinical_idempotent
  : nat_canonicalize (nat_canonicalize clinical_raw) = nat_canonicalize clinical_raw.
Proof. native_compute. reflexivity. Qed.

(** ** VII. Satellite telemetry — LEO constellation housekeeping.

    A ground station ingests housekeeping frames from a constellation
    of four LEO satellites.  Frames arrive out of order due to
    store-and-forward; two are superseded by on-board corrections;
    one satellite is deorbited and its final telemetry is cancelled.

    Encoding: ids are frame ids (71-78); timestamps are pass
    numbers (1-30); payloads encode battery voltage in hundredths
    of a volt (e.g. 812 = 8.12 V). *)

Definition satellite_raw : list nat_event :=
  [ orig  71 1 0 812    (* sat-A: battery 8.12 V *)
  ; orig  72 2 0 795    (* sat-B: battery 7.95 V *)
  ; orig  73 3 0 831    (* sat-C: battery 8.31 V *)
  ; orig  74 4 0 764    (* sat-D: battery 7.64 V *)
  ; corr  71 1 1 810    (* sat-A on-board recal: 8.10 V *)
  ; orig  75 10 0 808   (* sat-A: next pass, 8.08 V *)
  ; orig  76 12 0 791   (* sat-B: next pass, 7.91 V *)
  ; cancl 74 4 1        (* sat-D deorbited — discard frame *)
  ; orig  77 11 0 829   (* sat-C: next pass, 8.29 V *)
  ; corr  72 2 1 797    (* sat-B ground recal: 7.97 V *)
  ; orig  73 3 0 831    (* stale replay from store-and-forward *)
  ; orig  78 20 0 805   (* sat-A: third pass, 8.05 V *)
  ; orig  72 2 0 795    (* another stale replay, sat-B *)
  ].

Eval compute in (nat_canonicalize satellite_raw).
(* Seven frames survive (sat-D's deorbited frame is gone).
   Sat-A's first frame is corrected; sat-B's is recalibrated.
   Duplicates from store-and-forward are absorbed. *)

Eval compute in (nat_detect_gaps satellite_raw).
(* = [74]  — the deorbited satellite's frame. *)

Example satellite_triple_idempotent :
  let c := nat_canonicalize satellite_raw in
  nat_canonicalize (nat_canonicalize c) = c.
Proof. native_compute. reflexivity. Qed.

(** * Extraction. *)

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Extraction "eventstream.ml"
  canonicalize fold_stream sort_events apply_events process_one
  event_leb event_eqb detect_gaps
  IdMap replace_or_add_map apply_events_map map_values.
