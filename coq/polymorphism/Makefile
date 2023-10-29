
Makefile.coq: _CoqProject
ifeq ($(wildcard Makefile.coq),)
	coq_makefile -f _CoqProject -o Makefile.coq
else
endif

include Makefile.coq

clean::
	rm -f Makefile.coq Makefile.coq.bak
