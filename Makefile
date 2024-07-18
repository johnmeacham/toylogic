
.SUFFIXES:

HC = ghc
GHCOPTS=  -fglasgow-exts

all: Hilbert


Hilbert: Hilbert.hs
	ghc -O --make $<

clean:
	rm -f -- Hilbert $(BUILTSOURCES) *.o *.hi

