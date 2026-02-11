COQC    ?= coqc
OCAMLC  ?= ocamlc

EXTRACTED = eventstream.mli eventstream.ml
COMMON    = $(EXTRACTED) eventstream_functor.ml int_instance.ml

.PHONY: all extract test test-random test-fix fix-engine demo bench clean

all: test test-random test-fix fix-engine

# --- Coq ---

extract: $(EXTRACTED)

eventstream.vo $(EXTRACTED): eventstream.v
	$(COQC) $<

# --- OCaml ---

test.exe: $(COMMON) main.ml
	$(OCAMLC) $(COMMON) main.ml -o $@

test-random.exe: $(COMMON) test_random.ml
	$(OCAMLC) $(COMMON) test_random.ml -o $@

test-fix.exe: $(COMMON) fix_engine.ml test_fix.ml
	$(OCAMLC) $(COMMON) fix_engine.ml test_fix.ml -o $@

fix-engine.exe: $(COMMON) fix_engine.ml fix_engine_main.ml
	$(OCAMLC) $(COMMON) fix_engine.ml fix_engine_main.ml -o $@

# --- Run ---

test: test.exe
	ocamlrun $<

test-random: test-random.exe
	ocamlrun $<

test-fix: test-fix.exe
	ocamlrun $<

fix-engine: fix-engine.exe

demo: fix-engine.exe
	ocamlrun $< --demo

bench: fix-engine.exe
	ocamlrun $< --bench

# --- Clean ---

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux *.cmo *.cmi *.exe .lia.cache
