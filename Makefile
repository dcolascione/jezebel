EMACS=emacs
elfiles:=$(wildcard *.el)
all: $(elfiles:.el=.elc)

%.elc: %.el
	$(EMACS) -Q -batch -l shut-up-about-cl -f batch-byte-compile $<

clean:
	rm -f *.elc
