GHC      := ghc -fwarn-missing-fields -package lang -package util
GHCFLAGS := -i../.. -i../../Misc

# -fwarn-deprecations -fwarn-hi-shadowing -fwarn-simple-patterns -fwarn-overlapping-patterns -fwarn-missing-fields -fwarn-missing-methods -fwarn-unused-binds -fwarn-unused-imports # -prof -auto-all # -fwarn-incomplete-patterns   # -prof -auto-all #  # -prof -auto-all 

HAPPY      := happy
HAPPYFLAGS := -a -g -iparser.info 


all:	Parser.hs
	$(GHC) $(GHCFLAGS) --make Test

Parser.hs:	Parser.y Lexer.hs Tokens.hs ParserMisc.hs ../External.hs ../SrcInfo.hs ../SrcCommand.hs ../Token.hs #../../Misc/ErrorMsg.hs ../../Misc/Defaults.hs ../../Misc/Utils.hs
		$(HAPPY) $(HAPPYFLAGS) Parser.y

clean:	
	rm -fr *.o *.hi Parser.hs
