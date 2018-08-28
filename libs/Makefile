all: Makefile.coq
	+make -f Makefile.coq all

html: Makefile.coq
	+make -f Makefile.coq html

gallinahtml: Makefile.coq
	+make -f Makefile.coq gallinahtml

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq 

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject >Makefile.coq

.PHONY: all html gallinahtml clean
