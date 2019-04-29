include Makefile.coq

Makefile.coq: _CoqProjectWip
	coq_makefile -f _CoqProjectWip -o Makefile.coq
