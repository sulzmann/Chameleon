GHC      := ghc -package lang -package util
GHCFLAGS := -i..

# -fwarn-deprecations -fwarn-hi-shadowing -fwarn-simple-patterns -fwarn-overlapping-patterns -fwarn-missing-fields -fwarn-missing-methods -fwarn-unused-binds -fwarn-unused-imports # -prof -auto-all # -fwarn-incomplete-patterns   # -prof -auto-all #  # -prof -auto-all

HAPPY      := happy
HAPPYFLAGS := -a -g -d -iparser.info

all:	
	$(GHC) $(GHCFLAGS) --make Test.hs

clean:	
	rm -fr *.o *.hi
