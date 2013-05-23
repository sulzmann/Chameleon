#-------------------------------------------------------------------------
#  The Lazy Virtual Machine.
#
#  Daan Leijen.
#
#  Copyright 2001, Daan Leijen. All rights reserved. This file is
#  distributed under the terms of the GNU Library General Public License.
#-------------------------------------------------------------------------

# $Id$ *

include ../config/makefile

NDEBUG = yes

ifdef NDEBUG
CCOPT	   = -O2 $(CCOPTS) -I. -Icommon
LINKOPT    = $(LINKOPTS)
CCOPT_FAST = -O3 $(CCOPTS) -I. -Icommon
else
 ifdef TRACE
CCOPT	   = $(CCOPTS) -I. -Icommon -DDEBUG -DTRACE_TRACE -DTRACE_INSTR -DTRACE_STACK
LINKOPT    = $(LINKOPTS)
CCOPT_FAST = $(CCOPTS) -I. -Icommon -DDEBUG -DTRACE_TRACE -DTRACE_INSTR -DTRACE_STACK
 else
CCOPT	   = $(CCOPTS) -I. -Icommon
LINKOPT    = $(LINKOPTS)
CCOPT_FAST = $(CCOPTS) -I. -Icommon
 endif
endif

CORE	= main.c stats.c options.c \
	  schedule.c evaluator.c instr.c thread.c stack.c \
	  loader.c module.c print.c \
	  ccall.c dynamic.c \
	  fail.c misc.c signals.c systhread.c sys.c primfloat.c

HEAP	= fixed.c bytes.c \
	  alloc.c compact.c custom.c finalise.c freelist.c gc_ctrl.c \
	  major_gc.c minor_gc.c memory.c roots.c weak.c globroots.c

PRIM	= prims.c \
	  primio.c primsys.c primstring.c

SRCS	= $(patsubst %,core/%,$(CORE)) $(patsubst %,heap/%,$(HEAP)) $(patsubst %,prim/%,$(PRIM))
OBJS	= $(SRCS:.c=.o)


#lvmrun$(EXE): $(OBJS)
#	$(LINK) -o $@ $(LINKOPT) $(OBJS) -g

lvmrun$(EXE): $(OBJS)
	$(LINK) -o $@ $(LINKOPT) $(OBJS)
	$(STRIP) $@

core/evaluator.o: core/evaluator.c
	$(CC) -o $@ -c $< $(CCOPT_FAST)


.SUFFIXES: .c .o

.c.o:
	$(CC) -o $@ -c $< $(CCOPT)

clean:
	$(RM) core/*.o heap/*.o prim/*.o lvmrun$(EXE)
	$(RM) runtime.ncb runtime.opt runtime.plg *.obj

# dependencies
# [gcc -MM] generates the dependencies without the full
# directory name, ie.
#  evaluator.o: ...
# instead of
#  core/evaluator.o: ..
# we therefore use [sed] to append the directory name
depend:
	$(CC) -MM $(CCOPT) core/*.c > .depend.temp
	sed -e 's/\(.*\.o\)/core\/\1/' .depend.temp >  .depend
	$(CC) -MM $(CCOPT) heap/*.c > .depend.temp
	sed -e 's/\(.*\.o\)/heap\/\1/' .depend.temp >> .depend
	$(CC) -MM $(CCOPT) prim/*.c > .depend.temp
	sed -e 's/\(.*\.o\)/prim\/\1/' .depend.temp >> .depend
	$(RM) .depend.temp

include .depend