all: Makefile.coq
	+make -f Makefile.coq all

meta:
	cd metacoq && ./configure.sh local && make checker -j 8

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -f website/*html
	rm -f */*.coq
	rm -f */Makefile.coq
	rm -f */Makefile.coq.conf
	rm -f .*.aux
	rm -f *.v~
	rm -f */.*.aux
	rm -f */Makefile~
	rm -f */*.glob
	rm -f */*.vo
	rm -f */.*.d
	rm -f */*.v~

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq


website: Makefile.coq
	+make -f Makefile.coq html
	mv html/*html website
	rm -rf html

.PHONY: all clean website
