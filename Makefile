COQC    ?= coqc
OCAMLC  ?= ocamlc

SRC       = src/eventstream.mli src/eventstream.ml src/eventstream_functor.ml src/int_instance.ml
OCFLAGS   = -I src -I test
BUILD     = build

.PHONY: all extract test test-random test-fix fix-engine demo bench clean

all: test test-random test-fix fix-engine

# --- Coq ---

extract: src/eventstream.ml

proof/eventstream.vo src/eventstream.ml: proof/eventstream.v
	cd proof && $(COQC) eventstream.v
	git checkout src/eventstream.mli

# --- OCaml ---

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/test.exe: $(SRC) test/main.ml | $(BUILD)
	$(OCAMLC) $(OCFLAGS) $(SRC) test/main.ml -o $@

$(BUILD)/test-random.exe: $(SRC) test/test_random.ml | $(BUILD)
	$(OCAMLC) $(OCFLAGS) $(SRC) test/test_random.ml -o $@

$(BUILD)/test-fix.exe: $(SRC) src/fix_engine.ml test/test_fix.ml | $(BUILD)
	$(OCAMLC) $(OCFLAGS) $(SRC) src/fix_engine.ml test/test_fix.ml -o $@

$(BUILD)/fix-engine.exe: $(SRC) src/fix_engine.ml src/fix_engine_main.ml | $(BUILD)
	$(OCAMLC) $(OCFLAGS) $(SRC) src/fix_engine.ml src/fix_engine_main.ml -o $@

# --- Run ---

test: $(BUILD)/test.exe
	ocamlrun $<

test-random: $(BUILD)/test-random.exe
	ocamlrun $<

test-fix: $(BUILD)/test-fix.exe
	ocamlrun $<

fix-engine: $(BUILD)/fix-engine.exe

demo: $(BUILD)/fix-engine.exe
	ocamlrun $< --demo

bench: $(BUILD)/fix-engine.exe
	ocamlrun $< --bench

# --- Clean ---

clean:
	rm -rf $(BUILD)
	rm -f proof/*.vo proof/*.vos proof/*.vok proof/*.glob proof/.*.aux proof/.lia.cache
	rm -f src/*.cmo src/*.cmi test/*.cmo test/*.cmi
