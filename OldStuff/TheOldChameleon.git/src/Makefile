INSTALL_PATH="\"$(HOME)/Projects/chameleon/\""
#GHC=ghc
#GHC=/home/bjpop/bin/ghc

#INSTALL_PATH="\/home/luzm/chameleon/" #    "\"$(CHAMELEONDIR)/\""
GHC= ghc6
GHCFLAGS= -DINSTALL_PATH=$(INSTALL_PATH) # -O2 # -prof -auto-all # -O2

HSFILES=AST/*.hs AST/ChParser/*.hs Backends/*.hs Backends/Scheme/*.hs Config/*.hs Core/*.hs Core/Kinds/*.hs Misc/*.hs Misc/Output/*.hs Solvers/*.hs System/*.hs System/Chameleon/*.hs System/Typo/*.hs TypeError/*.hs Backends/Lvm/*.hs Backends/Lvm/asm/*.hs Backends/Lvm/common/*.hs Backends/Lvm/core/*.hs Backends/Lvm/lvm/*.hs

LVMPATHS=Backends/Lvm/Asm:Backends/Lvm/Common:Backends/Lvm/Core:Backends/Lvm/Lvm:Backends/Lvm/Common/ghc

################################################################################

all:		parser herbie ch-main

mac:		parser herbie-mac ch-main

ch-main:	
		$(GHC) $(GHCFLAGS) -fglasgow-exts -package base Solvers/herbie.o -iMisc -i$(LVMPATHS) --make System/Chameleon/Main.hs -o chameleon	
#		$(GHC) $(GHCFLAGS) -fglasgow-exts -package text -package lang Solvers/herbie.o -iMisc -i$(LVMPATHS) --make System/Chameleon/Main.hs -o chameleon	

parser:	
		make -C AST/ChParser Parser.hs

herbie:		
		make -C Solvers/ herbie

herbie-mac:	
		make -C Solvers/ herbie-no-memalign

########################################

typo:		parser herbie typo-main

typo-mac:	parser herbie-mac typo-main

typo-main:	
		$(GHC) $(GHCFLAGS) -fglasgow-exts -package lang -package wx Solvers/herbie.o -iMisc --make System/Typo/Main.hs -o typo


########################################

haddock:	
		rm -fr AST/ChParser/Parser.hs ; \
		haddock -h -o ../doc/haddock $(HSFILES)

########################################

clean:	
	rm -fr *.o *.hi ; \
	make -C AST clean ; \
	make -C AST/ChParser clean ; \
	make -C Core clean ; \
	make -C Config clean ; \
	make -C Misc clean ; \
	make -C Solvers clean ; \
	make -C TypeError clean ; \
	make -C System clean ; \
	make -C Backends clean ; \
	make -C X clean ;
