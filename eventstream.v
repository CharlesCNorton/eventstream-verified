(******************************************************************************)
(*                                                                            *)
(*              Deterministic Event-Stream Canonicalization                   *)
(*                                                                            *)
(*     Duplication, reordering, corrections, and cancels over a raw event     *)
(*     stream reduced to a canonical truth stream.                            *)
(*                                                                            *)
(*     Proven properties:                                                     *)
(*       - Determinism: canonicalize is permutation-invariant.                *)
(*       - Idempotence: canonicalize (canonicalize x) = canonicalize x.       *)
(*       - Sort correctness: output is a sorted permutation of the input.     *)
(*       - No cancel leakage: cancel events are consumed, never emitted.      *)
(*       - Unique ids: each event id appears at most once in output.          *)
(*                                                                            *)
(*     Serves as the replay-safe ingestion layer for any data product         *)
(*     or analytics pipeline that must be bit-for-bit reproducible.           *)
(*                                                                            *)
(*     Note on extraction: nat is mapped to OCaml int via ExtrOcamlNatInt.    *)
(*     Insertion sort is used for proof clarity; production deployments        *)
(*     should substitute Coq.Sorting.Mergesort (same interface, O(n log n)).  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: February 10, 2026                                                *)
(*     License: Proprietary - All Rights Reserved                             *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
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

Record event : Type := mkEvent {
  ev_id : nat;
  ev_timestamp : nat;
  ev_seq : nat;
  ev_payload : nat;
  ev_kind : event_kind
}.

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
  Nat.eqb (ev_id e1) (ev_id e2) &&
  Nat.eqb (ev_timestamp e1) (ev_timestamp e2) &&
  Nat.eqb (ev_seq e1) (ev_seq e2) &&
  Nat.eqb (ev_payload e1) (ev_payload e2) &&
  event_kind_eqb (ev_kind e1) (ev_kind e2).

Lemma event_eqb_spec
  : forall e1 e2, reflect (e1 = e2) (event_eqb e1 e2).
Proof.
  intros [id1 ts1 sq1 pl1 k1] [id2 ts2 sq2 pl2 k2].
  unfold event_eqb; simpl.
  destruct (Nat.eqb_spec id1 id2);
  destruct (Nat.eqb_spec ts1 ts2);
  destruct (Nat.eqb_spec sq1 sq2);
  destruct (Nat.eqb_spec pl1 pl2);
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

Definition event_keys (e : event) : list nat :=
  [ev_timestamp e; ev_seq e; ev_id e; ev_payload e; kind_index (ev_kind e)].

Lemma event_keys_injective
  : forall e1 e2, event_keys e1 = event_keys e2 -> e1 = e2.
Proof.
  intros [id1 ts1 sq1 pl1 k1] [id2 ts2 sq2 pl2 k2].
  unfold event_keys. simpl.
  intro H. injection H. intros Hk Hp Hi Hs Ht.
  f_equal; try assumption.
  apply kind_index_injective. exact Hk.
Qed.

Definition event_leb (e1 e2 : event) : bool :=
  lex_leb (event_keys e1) (event_keys e2).

Lemma event_leb_refl
  : forall e, event_leb e e = true.
Proof.
  intro e. unfold event_leb. apply lex_leb_refl.
Qed.

Lemma event_leb_total
  : forall e1 e2, event_leb e1 e2 = true \/ event_leb e2 e1 = true.
Proof.
  intros e1 e2. unfold event_leb. apply lex_leb_total.
Qed.

Lemma event_leb_antisym
  : forall e1 e2, event_leb e1 e2 = true -> event_leb e2 e1 = true -> e1 = e2.
Proof.
  intros e1 e2 H1 H2. unfold event_leb in *.
  apply event_keys_injective. apply lex_leb_antisym; assumption.
Qed.

Lemma event_leb_trans
  : forall e1 e2 e3,
    event_leb e1 e2 = true -> event_leb e2 e3 = true -> event_leb e1 e3 = true.
Proof.
  intros e1 e2 e3 H1 H2. unfold event_leb in *.
  apply lex_leb_trans with (event_keys e2); assumption.
Qed.

(** * Insertion sort on events.
    Proof-friendly. For production extraction, substitute Coq.Sorting.Mergesort
    which provides the same Permutation + Sorted interface at O(n log n). *)

Fixpoint insert (e : event) (l : list event) : list event :=
  match l with
  | [] => [e]
  | h :: t =>
    if event_leb e h then e :: h :: t
    else h :: insert e t
  end.

Fixpoint sort_events (l : list event) : list event :=
  match l with
  | [] => []
  | h :: t => insert h (sort_events t)
  end.

(** * Sort correctness: output is a sorted permutation. *)

Inductive Sorted_leb : list event -> Prop :=
  | Sorted_leb_nil : Sorted_leb []
  | Sorted_leb_one : forall e, Sorted_leb [e]
  | Sorted_leb_cons : forall e1 e2 l,
      event_leb e1 e2 = true ->
      Sorted_leb (e2 :: l) ->
      Sorted_leb (e1 :: e2 :: l).

Lemma insert_perm
  : forall e l, Permutation (e :: l) (insert e l).
Proof.
  intros e l. induction l as [| h t IH]; simpl.
  - apply Permutation_refl.
  - destruct (event_leb e h).
    + apply Permutation_refl.
    + apply perm_trans with (h :: e :: t).
      * apply perm_swap.
      * apply perm_skip. exact IH.
Defined.

Theorem sort_events_perm
  : forall l, Permutation l (sort_events l).
Proof.
  induction l as [| h t IH]; simpl.
  - apply perm_nil.
  - apply perm_trans with (h :: sort_events t).
    + apply perm_skip. exact IH.
    + apply insert_perm.
Defined.

Lemma insert_sorted
  : forall e l, Sorted_leb l -> Sorted_leb (insert e l).
Proof.
  intros e l Hs. induction Hs; simpl.
  - apply Sorted_leb_one.
  - destruct (event_leb e e0) eqn:Hle.
    + apply Sorted_leb_cons; [ exact Hle | apply Sorted_leb_one ].
    + apply Sorted_leb_cons.
      * destruct (event_leb_total e e0); [ rewrite Hle in H; discriminate | exact H ].
      * apply Sorted_leb_one.
  - destruct (event_leb e e1) eqn:Hle.
    + apply Sorted_leb_cons; [ exact Hle | apply Sorted_leb_cons; [ exact H | exact Hs ] ].
    + simpl. destruct (event_leb e e2) eqn:Hle2.
      * apply Sorted_leb_cons.
        -- destruct (event_leb_total e e1); [ rewrite Hle in H0; discriminate | exact H0 ].
        -- apply Sorted_leb_cons; [ exact Hle2 | exact Hs ].
      * apply Sorted_leb_cons; [ exact H | ].
        simpl in IHHs. rewrite Hle2 in IHHs. exact IHHs.
Defined.

Theorem sort_events_sorted
  : forall l, Sorted_leb (sort_events l).
Proof.
  induction l as [| h t IH]; simpl.
  - apply Sorted_leb_nil.
  - apply insert_sorted. exact IH.
Defined.

(** * Sort helpers. *)

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

Lemma sort_sorted_id
  : forall l, Sorted_leb l -> sort_events l = l.
Proof.
  induction l as [| h t IHl]; simpl; intro Hs.
  - reflexivity.
  - rewrite (IHl (Sorted_leb_tail h t Hs)).
    destruct t as [| h2 t2]; simpl.
    + reflexivity.
    + rewrite (Sorted_leb_head_leb h h2 t2 Hs). reflexivity.
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

(** * Event processing. *)

Fixpoint replace_or_add (e : event) (acc : list event) : list event :=
  match acc with
  | [] => [e]
  | h :: t =>
    if Nat.eqb (ev_id h) (ev_id e) then
      if Nat.leb (ev_seq h) (ev_seq e) then e :: t
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
      apply_events rest (filter (fun x => negb (Nat.eqb (ev_id x) (ev_id e))) acc)
    end
  end.

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
  - destruct (Nat.eqb (ev_id h) (ev_id e)).
    + destruct (Nat.leb (ev_seq h) (ev_seq e)).
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
    + apply IH. apply filter_no_cancels. exact Hacc.
Defined.

(** * Unique ids in output. *)

Definition ids_of (l : list event) : list nat := map ev_id l.

Lemma replace_or_add_on_fresh_id
  : forall e acc,
    ~ In (ev_id e) (ids_of acc) -> replace_or_add e acc = acc ++ [e].
Proof.
  intros e acc. induction acc as [| h t IH]; simpl; intro Hfresh.
  - reflexivity.
  - destruct (Nat.eqb (ev_id h) (ev_id e)) eqn:Heq.
    + apply Nat.eqb_eq in Heq. exfalso. apply Hfresh. left. exact Heq.
    + f_equal. apply IH. intro Hin. apply Hfresh. right. exact Hin.
Defined.

Lemma replace_or_add_ids
  : forall e acc,
    ids_of (replace_or_add e acc) =
    if existsb (fun x => Nat.eqb (ev_id x) (ev_id e)) acc
    then ids_of acc
    else ids_of acc ++ [ev_id e].
Proof.
  intros e acc. induction acc as [| h t IH]; simpl.
  - reflexivity.
  - destruct (Nat.eqb (ev_id h) (ev_id e)) eqn:Heq; simpl.
    + destruct (Nat.leb (ev_seq h) (ev_seq e)); simpl.
      * unfold ids_of. simpl. apply Nat.eqb_eq in Heq. rewrite Heq. reflexivity.
      * reflexivity.
    + unfold ids_of in *. simpl.
      rewrite IH.
      destruct (existsb (fun x => Nat.eqb (ev_id x) (ev_id e)) t); reflexivity.
Defined.

Lemma NoDup_replace_or_add
  : forall e acc, NoDup (ids_of acc) -> NoDup (ids_of (replace_or_add e acc)).
Proof.
  intros e acc Hnd. induction acc as [| h t IH]; simpl.
  - apply NoDup_cons. { simpl. auto. } apply NoDup_nil.
  - destruct (Nat.eqb (ev_id h) (ev_id e)) eqn:Heq.
    + destruct (Nat.leb (ev_seq h) (ev_seq e)).
      * apply Nat.eqb_eq in Heq.
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
        destruct (existsb (fun x => Nat.eqb (ev_id x) (ev_id e)) t).
        -- exact Hin.
        -- apply in_app_or in Hin. destruct Hin as [Hin | Hin].
           ++ exact Hin.
           ++ simpl in Hin. destruct Hin as [Hin | []].
              apply Nat.eqb_neq in Heq. exfalso. apply Heq. symmetry. exact Hin.
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
    ids_of (filter (fun x => negb (Nat.eqb (ev_id x) id)) l) =
    filter (fun x => negb (Nat.eqb x id)) (ids_of l).
Proof.
  intros id l. unfold ids_of.
  induction l as [| a t IH]; simpl.
  - reflexivity.
  - destruct (negb (Nat.eqb (ev_id a) id)) eqn:Hf; simpl; rewrite IH; reflexivity.
Defined.

Lemma apply_events_NoDup
  : forall stream acc, NoDup (ids_of acc) -> NoDup (ids_of (apply_events stream acc)).
Proof.
  intros stream. induction stream as [| e rest IH]; simpl; intros acc Hnd.
  - exact Hnd.
  - destruct (ev_kind e); apply IH.
    + apply NoDup_replace_or_add. exact Hnd.
    + apply NoDup_replace_or_add. exact Hnd.
    + rewrite filter_ids_comm. apply NoDup_filter. exact Hnd.
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

(** * Gap detection: find event ids present in the stream but absent
    from the canonical output, indicating they were cancelled or
    superseded without replacement. *)

Fixpoint mem_nat (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => Nat.eqb n h || mem_nat n t
  end.

Fixpoint dedup_nat (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t =>
    if mem_nat h t then dedup_nat t
    else h :: dedup_nat t
  end.

Definition detect_gaps (stream : list event) : list nat :=
  let input_ids := dedup_nat (ids_of stream) in
  let output_ids := ids_of (canonicalize stream) in
  filter (fun id => negb (mem_nat id output_ids)) input_ids.

(** * Extraction. *)

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Extraction "D:/eventstream-verified/eventstream.ml"
  canonicalize sort_events apply_events
  event_leb event_eqb detect_gaps.
