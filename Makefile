.DELETE_ON_ERROR:

v := $(wildcard *.v)
vo := $(v:.v=.vo)
vok := $(v:.v=.vok)
vos := $(v:.v=.vos)
glob := $(v:.v=.glob)

.PHONY: all clean

all: $(vo)

%.vo : %.v
	coqc $<

clean :
	rm -f $(vo) $(vok) $(vos) $(glob)


Function.vo : Alphabet.vo
Computation.vo : Alphabet.vo Function.vo
Turing.vo : Alphabet.vo Computation.vo Function.vo
LIMP.vo : Alphabet.vo Computation.vo Function.vo
