COQDOCJS_DIR ?= coqdocjs
EXTRA_DIR = $(COQDOCJS_DIR)/extra
COQDOCFLAGS ?= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
	--coqlib_url 'https://rocq-prover.org/doc/V9.1.0/corelib/' \
	--external 'https://math-comp.github.io/htmldoc_2_5_0/' mathcomp \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE ?= Makefile.coq
COQDOCJS_LN ?= false

.PHONY: all clean install coqdoc

all clean install: Makefile.coq
	$(MAKE) -f $< $@

%.vo: Makefile.coq %.v
	$(MAKE) -f $< $@

Makefile.coq: _CoqProject
	$(COQBIN)rocq makefile -f $< -o $@


%: Makefile.coq
	$(MAKE) -f $< $@

coqdoc: $(COQMAKEFILE)
	$(MAKE) -f $^ html
ifeq ($(COQDOCJS_LN),true)
	ln -sf ../$(EXTRA_DIR)/resources html
else
	cp -R $(EXTRA_DIR)/resources html
endif
