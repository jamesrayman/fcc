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


Run.vo : Turing.vo
Turing.vo : Alphabet.vo
Language.vo : Alphabet.vo
UTM.vo: Run.vo Alphabet.vo Turing.vo
