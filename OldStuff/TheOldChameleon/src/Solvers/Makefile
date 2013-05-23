all:	herbie.o

herbie:	herbie.c
	gcc -g -Wall -c herbie.c

herbie-no-memalign:	herbie.c
			gcc -O3 -Wall -DSYS_MACOSX -c herbie.c

main:
	gcc -O3 -finline-functions -fomit-frame-pointer -c -Wall herbie.c
	ghc -i.. -O2 -o chr_test -fffi -fglasgow-exts --make Test.hs herbie.o

clean:	
	rm -fr *.hi *.o
