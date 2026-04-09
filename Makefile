.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

clean:
	test -f Makefile.coq && $(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq Makefile.coq.conf
