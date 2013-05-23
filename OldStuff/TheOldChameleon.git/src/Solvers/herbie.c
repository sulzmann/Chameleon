/* herbie 1.0 -- Herbrand solver for GHC
   Copright (C) 2004 Gregory J. Duck
   (Modified/Improved by The Chameleon Team)

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA 
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

// NOTE: memalign is not provided in MacOS X, but malloc is guaranteed to
//	 return 16-byte aligned blocks. (We assume 32 bit pointers
//	 everywhere -- what a crappy assumption.)
#ifdef SYS_MACOSX
#define memalign(a,s)	malloc(s)
#include <malloc/malloc.h>
#else
#include <malloc.h>
#endif

// #define HERBIE_DEBUG
  
#define HERBRAND_STORE_SIZE	512
#define VAR_TAG				0
#define CONST_TAG			1
#define APP_TAG				2
#define SPECIAL_TAG         3
#define GET_TAG(term)       (((unsigned)(term))&0x00000003)
#define GET_PTR(term)       ((word_t *)(((unsigned)(term))&0xFFFFFFFC))
#define SET_TAG(term,tag)   ((word_t *)(((unsigned)(term))+(tag)))
#define APP_ARG(app,arg)	((word_t *)(GET_PTR(app)[arg]))
#define SAME_PTR(var1,var2)	(((unsigned)(var1))==((unsigned)(var2)))
#define DEREF(term)         \
    while((GET_TAG(term) == VAR_TAG) && (*(term) != (word_t)(term))) \
        (term) = (word_t *)(*GET_PTR(term))

/* Unification modes */
#define UNIFICATION			0
#define MATCHING			1
#define ENTAILMENT          2
#define VARIANCE            3

/* Herbrand solver flags. */
/* WARNING: Must be consistent with Herbie.hs */
#define NO_REWIND_HEAP      0x00000001
#define NO_OCCURS_CHECK     0x00000002
#define NO_TRAIL            0x00000004
#define FLAG_ON(store,flag) (((store)->flags)&(flag))

/* Failure reasons. */
#define SUCCESS				0
#define FAIL_MISMATCH		1
#define FAIL_OCCURS_CHECK	2
#define FAIL_MATCHING		3

/* Must be a value less than 2^16 */
#define SYMBOL_TABLE_SIZE       1024
#define MAX_CHAIN_SIZE          0x00003FFF
#define SYMBOL_CODE(hash,count) (((hash)<<16)|(((count)&MAX_CHAIN_SIZE)<<2))
#define GET_HASHVAL(code)       ((code)>>16)
#define GET_COUNT(code)         (((code)&0x0000FFFF)>>2)

typedef struct __bucket_s {
        char *symbol;
        struct __bucket_s *next;
} bucket_s;

static bucket_s *table[SYMBOL_TABLE_SIZE] = {NULL};

typedef unsigned word_t;

typedef struct __herbrand_store_s {
	word_t heap[HERBRAND_STORE_SIZE];
    word_t *trail;
	unsigned trail_size;
	unsigned trail_usage;
	struct __herbrand_store_s *next_store;
    struct __herbrand_store_s *prev_store;
	struct __herbrand_store_s *last_store;
	unsigned usage;
    unsigned id;
    unsigned flags;
} store_s;

static store_s *make_new_store(unsigned use_id);
static void *store_alloc(store_s *store,unsigned size);
/* static void *store_alloc_bytes(store_s *store,unsigned size); */
static void trail_current_value(store_s *store,word_t *ptr);
static void trail_ptr_value(store_s *store,word_t *ptr,word_t value);
static int do_unification(store_s *store,int mode,word_t *term1,word_t *term2);
static int is_var_in_term(word_t *var,word_t *term);
static void rewind_heap(store_s *store,unsigned id,unsigned usage);
static word_t get_symbol_code(const char *symbol);
extern char *get_code_symbol(word_t *code);
static void print_term_rec(word_t *term,FILE *file);
#ifdef HERBIE_DEBUG
static void debug_unify(const char *fn,char c,word_t *term1,word_t *term2);
#endif


/* Use this functor when building eq. constraints */
char eq_string[] = "=";

/* Creates a new Herbrand store for use. */
extern store_s *new_store(void)
{
    return make_new_store(0);
}

static store_s *make_new_store(unsigned use_id)
{
	store_s *store = (store_s *)memalign(4,sizeof(store_s));

#ifdef HERBIE_DEBUG
	fprintf(stderr,"herbie: allocating store %d\n",use_id);
#endif
    if(store == NULL) {
        fprintf(stderr,"herbie: (FATAL) failed to allocate %u bytes"
                " for Herbrand store: %s\n",
                sizeof(store_s),strerror(errno));
        exit(EXIT_FAILURE);
    }
	store->trail       = NULL;
	store->trail_size  = 0;
	store->trail_usage = 0;
	store->next_store  = NULL;
	store->prev_store  = NULL;
    store->last_store  = store;
	store->usage       = 0;
    store->id          = use_id;
    store->flags       = 0;
	return store;
}

/* Frees an old unwanted Herbrand store. */
extern void delete_store(store_s *store)
{
	store_s *next;
	
	while(store != NULL) {
		next = store->next_store;
		free(store->trail);
        free(store);
		store = next;
	}
}

/* Allocates `size' words from store. */
static void *store_alloc(store_s *store,unsigned size)
{
	store_s *last, *new;
	void *ptr;
	
	last = store->last_store;
#ifdef HERBIE_DEBUG
	fprintf(stderr,"herbie: store_alloc(%d) %d %d\n",size,last->usage,
					last->id);
#endif
	if((HERBRAND_STORE_SIZE - last->usage) < size) {
		if(size > HERBRAND_STORE_SIZE) {
			fprintf(stderr,"herbie: (BUG) attempt to allocate %u words, maximum"
					" allowed is %u.\n",size,HERBRAND_STORE_SIZE);
			exit(EXIT_FAILURE);
		}
        new               = make_new_store(last->id+1);
        new->prev_store   = last;
		last->next_store  = new;
		store->last_store = new;
		last              = new;
	}
	
	ptr = (void *)(&(last->heap[last->usage]));
	last->usage += size;
	return ptr;
}

/* Allocates `size' bytes from store. */
/*
static void *store_alloc_bytes(store_s *store,unsigned size)
{
	return store_alloc(store,(size+sizeof(word_t)+1)/sizeof(word_t));
}
*/

/* Constructs a constant from a string. */
extern word_t *construct_const(store_s *store,char *name)
{
    return SET_TAG(get_symbol_code(name),CONST_TAG);
}

/* Constructs an application from two other terms. */
extern word_t *construct_app(store_s *store,word_t *arg1,word_t *arg2)
{
	word_t *app = (word_t *)store_alloc(store,2);
	app[0] = (word_t)arg1;
	app[1] = (word_t)arg2;
	return SET_TAG(app,APP_TAG);
}

/* Creates a fresh (free) Herbrand variable. */
extern word_t *fresh_var(store_s *store)
{
	word_t *var = (word_t *)store_alloc(store,1);
	*var = (word_t)SET_TAG(var,VAR_TAG);
	return SET_TAG(var,VAR_TAG);
}

/* Tests if the given term is a free variable. */
extern int is_var(word_t *term)
{
    DEREF(term);
#ifdef HERBIE_DEBUG    
    fprintf(stderr,"herbie: is_var(0x%x) = %d\n",term,
					(GET_TAG(term) == VAR_TAG));
#endif
    return (GET_TAG(term) == VAR_TAG);
}

/* Tests if the given term is a constant. */
extern int is_const(word_t *term)
{
    DEREF(term);
#ifdef HERBIE_DEBUG    
    fprintf(stderr,"herbie: is_cnst(0x%x) = %d\n",term,
                    (GET_TAG(term) == CONST_TAG));
#endif    
    return (GET_TAG(term) == CONST_TAG);
}

/* Tests if the given term is an application. */
extern int is_app(word_t *term)
{
    DEREF(term);
#ifdef HERBIE_DEBUG
    fprintf(stderr,"herbie: is_app(0x%x) = %d\n",term,
                    (GET_TAG(term) == APP_TAG));
#endif    
    return (GET_TAG(term) == APP_TAG);
}

/* Tests if the given term is a variable, without dereferencing it. */
extern int was_var(word_t *term)
{
#ifdef HERBIE_DEBUG    
    fprintf(stderr,"herbie: was_var(0x%x) = %d\n",term,
					(GET_TAG(term) == VAR_TAG));
#endif
    return (GET_TAG(term) == VAR_TAG);
}

/* Dereferences the variable. */
extern word_t *deref(word_t *term)
{
    DEREF(term);
    return term;
}

/* Returns an argument to an application .*/
extern word_t *app_arg(word_t *term,int arg)
{
    DEREF(term);
#ifdef HERBIE_DEBUG
    if((arg != 0) && (arg != 1)) {
        fprintf(stderr,"herbie: (BUG) app_arg argument must be either"
                " 0 or 1, got %d.\n",arg);
        exit(EXIT_FAILURE);
    } else if(!is_app(term)) {
        fprintf(stderr,"herbie: (BUG) app_arg applied to a non-application,"
                " tag = %d.\n",GET_TAG(term));
        exit(EXIT_FAILURE);
    }
#endif
    return APP_ARG(term,arg);
}

/* Succeeds if var is not in term */
/* ASSUMPTION: 'var' and `term' are already derefed */
static int occurs_check(word_t *var,word_t *term)
{
	word_t *arg;
    
    switch(GET_TAG(term)) {
		case VAR_TAG:
			return !SAME_PTR(var,term);
		case CONST_TAG:
			return 1;
		case APP_TAG:
			arg = APP_ARG(term,0);
            DEREF(arg);
            if(occurs_check(var,arg)) {
                arg = APP_ARG(term,1);
                DEREF(arg);
				return occurs_check(var,arg);
            }
			return 0;
	}
	return 0;
}

/* Succeeds if term1 can be unified with term2 without further binding
 * any variables in term2 */
extern int match_term_term(store_s *store,word_t *term1,word_t *term2)
{
#ifdef HERBIE_DEBUG
    int result;
    debug_unify("match_term_term",'\n',term2,term1);
    result = do_unification(store,MATCHING,term2,term1);
    debug_unify("match_term_term",' ',term2,term1);
    fprintf(stderr,"= %d\n",result);
    return result;
#else
    return do_unification(store,MATCHING,term2,term1);
#endif
}

/* Normal Herbrand unification. */
extern int unify_term_term(store_s *store,word_t *term1,word_t *term2)
{
#ifdef HERBIE_DEBUG
    int result;
    debug_unify("unify_term_term",'\n',term1,term2);
    result = do_unification(store,UNIFICATION,term1,term2);
    debug_unify("unify_term_term",' ',term1,term2);
    fprintf(stderr,"= %d\n",result);
    return result;
#else
    return do_unification(store,UNIFICATION,term1,term2);
#endif
}

/* Tests if two terms are equal (a.k.a Prolog's ==). */
extern int entailment_term_term(store_s *store,word_t *term1,word_t *term2)
{
#ifdef HERBIE_DEBUG
    int result;
    debug_unify("entailment_term_term",'\n',term1,term2);
    result = do_unification(store,ENTAILMENT,term1,term2);
    debug_unify("entailment_term_term",' ',term1,term2);
    fprintf(stderr,"= %d\n",result);
    return result;
#else
    return do_unification(store,ENTAILMENT,term1,term2);
#endif
}

/* Tests if two terms are variant. */
extern int variant_term_term(store_s *store,word_t *term1,word_t *term2)
{
#ifdef HERBIE_DEBUG
    int result;
    debug_unify("variant_term_term",'\n',term1,term2);
    result = do_unification(store,VARIANCE,term1,term2);
    debug_unify("variant_term_term",' ',term1,term2);
    fprintf(stderr,"= %d\n",result);
    return result;
#else
    return do_unification(store,VARIANCE,term1,term2);
#endif
}

/* The implementation of the unification algorithm.  mode indicates if
 * we are doing unification, matching or entailment testing. */
static int do_unification(store_s *store,int mode,word_t *term1,word_t *term2)
{
	word_t *arg1, *arg2;
	int status;
	
	DEREF(term1);
	DEREF(term2); 

	switch(GET_TAG(term1)) {
		case VAR_TAG:
			if(mode != MATCHING) {
                if(GET_TAG(term2) != VAR_TAG) {
                    if(mode != UNIFICATION) /* mode == ENTAILMENT | VARIANCE */
                        return FAIL_MISMATCH;
				    if((!FLAG_ON(store,NO_OCCURS_CHECK)) && 
                            (!occurs_check(term1,term2)))
					    return FAIL_OCCURS_CHECK;
			    }
                /* Will fail if term2 is not a var. */
                if(SAME_PTR(term1,term2))
                    return SUCCESS;
                if(mode == ENTAILMENT) 
                    return FAIL_MISMATCH;
            }
            trail_current_value(store,term1);
            switch(mode) {
                case VARIANCE:
                    /* Note: term2 must be a variable. */
                    trail_current_value(store,term2);
                    *GET_PTR(term2) = 
                        (word_t)SET_TAG(term1,SPECIAL_TAG);
                    *GET_PTR(term1) = 
                        (word_t)SET_TAG(term1,SPECIAL_TAG);
                    return SUCCESS;
                case MATCHING:
                    /* Note: term2 must be a variable. */
                    if(GET_TAG(term2) == CONST_TAG) 
                        *GET_PTR(term1) = (word_t)term2;
                    else {
                        arg1 = store_alloc(store,1);
                        *arg1 = (word_t)term2;
                        *GET_PTR(term1) = (word_t)SET_TAG(arg1,SPECIAL_TAG);
                    }
                    return SUCCESS;
                default: /* case UNIFICATION */
                    *GET_PTR(term1) = (word_t)term2;
                    return SUCCESS;
            }
		case CONST_TAG:
			switch(GET_TAG(term2)) {
				case VAR_TAG:
                    /* mode == ENTAILMENT | VARIANCE | MATCHING */
                    if(mode != UNIFICATION)
                        return FAIL_MISMATCH;
					trail_current_value(store,term2);
					*GET_PTR(term2) = (word_t)term1;
					return SUCCESS;
				case CONST_TAG:
                    if((word_t)term1 != (word_t)term2)
						return FAIL_MISMATCH;
					return SUCCESS;
				default:
					return FAIL_MISMATCH;
			}
		case APP_TAG: 
			switch(GET_TAG(term2)) {
				case VAR_TAG:
                    /* mode == ENTAILMENT | VARIANCE | MATCHING */
                    if(mode != UNIFICATION)
                        return FAIL_MISMATCH;
		            if((!FLAG_ON(store,NO_OCCURS_CHECK)) &&
                            !occurs_check(term2,term1))
	                    return FAIL_OCCURS_CHECK;
					trail_current_value(store,term2);
					*GET_PTR(term2) = (word_t)term1;
					return SUCCESS;
				case CONST_TAG:
					return FAIL_MISMATCH;
				default:
					arg1 = APP_ARG(term1,0);
					arg2 = APP_ARG(term2,0);
					status = do_unification(store,mode,arg1,arg2);
					if(status)
						return status;
					arg1 = APP_ARG(term1,1);
					arg2 = APP_ARG(term2,1); 
					return do_unification(store,mode,arg1,arg2);
			}
		default:
            switch(mode) {
                case VARIANCE:
	                return SAME_PTR(term1,term2);
                default: /* case MATCHING */
                    return do_unification(store,ENTAILMENT,
                            (word_t *)*GET_PTR(term1),term2);
            }
    }
}

/* Skolemise a variable. */
extern void do_skolemise(store_s *store,word_t *term) 
{
    DEREF(term);
    trail_current_value(store,term);
    *GET_PTR(term) = (word_t)SET_TAG((word_t)term,SPECIAL_TAG);
}

/* Prints the given term. */
extern void print_term(word_t *term)
{
    print_term_rec(term,stdout);
    putchar('\n');
}

static void print_term_rec(word_t *term,FILE *file)
{
	DEREF(term);

	switch(GET_TAG(term)) {
		case VAR_TAG:
			fprintf(file,"t%x",(unsigned)term);
			return;
		case CONST_TAG:
			fputs(get_code_symbol(term),file);
			return;
		case APP_TAG:
			putc('(',file);
			print_term_rec(APP_ARG(term,0),file);
			fputs("@",file);
			print_term_rec(APP_ARG(term,1),file);
			putc(')',file);
			return;
		case SPECIAL_TAG:
			fprintf(file,"$<%x>",(unsigned)(GET_PTR(term)));
	}
}

/* Trails the current value of a pointer. */
static void trail_current_value(store_s *store,word_t *ptr)
{
#ifdef HERBIE_DEBUG
    fprintf(stderr,"herbie: trail_current_value(0x%x)\n",ptr);
#endif
	trail_ptr_value(store,ptr,*ptr);
}

/* Trail a ptr and a value. */
static void trail_ptr_value(store_s *store,word_t *ptr,word_t value)
{
#ifdef HERBIE_DEBUG
    fprintf(stderr,"herbie: trail_ptr_value(0x%x,0x%x)\n",(word_t)ptr,(word_t) value);
#endif
    
	if(!FLAG_ON(store,NO_TRAIL)) {
        if(store->trail_usage == store->trail_size) {
	    	store->trail_size = (2*store->trail_size + 32);
    		store->trail = (word_t *)realloc(store->trail,
    				store->trail_size*sizeof(word_t));
            if(store->trail == NULL) {
                fprintf(stderr,"herbie: (FATAL) failed to allocate %u bytes"
                    " for trail: %s\n",
                    store->trail_size*sizeof(word_t),strerror(errno));
                exit(EXIT_FAILURE);
            }
	    }

	    store->trail[store->trail_usage]   = (word_t)ptr;
        store->trail[store->trail_usage+1] = value;
	    store->trail_usage += 2;
    }
}

/* Create a new choicepoint. */
extern word_t create_choice_point(store_s *store)
{
    word_t cp_id;
	store_s *last = store->last_store;
	
#ifdef HERBIE_DEBUG
    fprintf(stderr,"herbie: create_choice_point(%d,%d)\n",last->usage,last->id);
#endif
	trail_ptr_value(store,NULL,last->id);
	cp_id = store->trail_usage;
	trail_ptr_value(store,NULL,last->usage);
#ifdef HERBIE_DEBUG
    fprintf(stderr,"herbie: create_choice_point = %d\n",cp_id);
#endif
    return cp_id;
}

/* Rewind the trail (and possibly the heap) to the given choicepoint. */
extern void rewind_trail(store_s *store,word_t cp_id)
{
	word_t old_usage, old_id;

#ifdef HERBIE_DEBUG
    fprintf(stderr,"herbie: rewind_trail(%d)\n",cp_id);
#endif
    store->trail_usage -= 2;
	do {
        if(store->trail[store->trail_usage] == (word_t)NULL) {
            if(store->trail_usage == cp_id) {
                old_usage = store->trail[store->trail_usage+1];
                store->trail_usage -= 2;
                old_id = store->trail[store->trail_usage+1];
                if(!FLAG_ON(store,NO_REWIND_HEAP))
                    rewind_heap(store,old_id,old_usage);
                return;
            } else
                store->trail_usage -= 4;
        } else {
		    *((word_t *)store->trail[store->trail_usage]) = 
			    store->trail[store->trail_usage+1];
		    store->trail_usage -= 2;
        }
	} while(1);
    return;
}

/* Rewind the heap (reclaim memory allocated since the choice point). */
static void rewind_heap(store_s *store,unsigned id,unsigned usage)
{
    store_s *curr = store->last_store, *prev;

#ifdef HERBIE_DEBUG
    fprintf(stderr,"herbie: rewind_heap(%d,%d)\n",id,usage);
#endif
	
    while(curr->id != id) {
        prev = curr;
        curr = curr->prev_store;
#ifdef HERBIE_DEBUG
		fprintf(stderr,"herbie: deleting store 0x%x.\n",(unsigned)prev);
#endif
        free(prev);
    }

    curr->usage       = usage;
    curr->next_store  = NULL;
    store->last_store = curr;

    return;
}

/* Copy the given term, like Prolog's copy_term. */
extern word_t *copy_term(store_s *store,word_t *term) 
{
    word_t *arg1, *arg2;

    DEREF(term);

    switch(GET_TAG(term)) {
        case VAR_TAG:
            arg1 = fresh_var(store);
            trail_current_value(store,term);
            *GET_PTR(term) = (word_t)SET_TAG((word_t)arg1,SPECIAL_TAG);
            return arg1;
        case CONST_TAG:
            return term;
        case APP_TAG: 
            arg1 = copy_term(store,APP_ARG(term,0));
            arg2 = copy_term(store,APP_ARG(term,1));
            return construct_app(store,arg1,arg2);
        default:    /* case SPECIAL_TAG */
            return SET_TAG((word_t)GET_PTR(term),VAR_TAG);
    }
}

/* Succeeds if `term' contains no free variables. */
extern int ground(word_t *term)
{
    DEREF(term);

    switch(GET_TAG(term)) {
        case VAR_TAG:
            return 0;
        case CONST_TAG:
            return 1;
        default:    /* case APP_TAG: */
            return (ground(APP_ARG(term,0)) && ground(APP_ARG(term,1)));
    }
}

/* Succeeds if `term1' and `term2' share at least one free variable. */
extern int share_variables(word_t *term1,word_t *term2)
{
    int result;
        
    DEREF(term1);
    
    switch(GET_TAG(term1)) {
        case VAR_TAG:
            return is_var_in_term(term1,term2);
        case CONST_TAG:
            return 0;
        default:    /* case APP_TAG: */
            result = share_variables(APP_ARG(term1,0),term2);
            if(result)
                return 1;
            return share_variables(APP_ARG(term1,1),term2);
    }
}

/* Succeeds if the given variable is in `term'. */
static int is_var_in_term(word_t *var,word_t *term)
{
    int result;
    DEREF(term);

    switch(GET_TAG(term)) {
        case VAR_TAG:
            return SAME_PTR(var,term);
        case CONST_TAG:
            return 0;
        default:    /* case APP_TAG: */
            result = is_var_in_term(var,APP_ARG(term,0));
            if(result)
                return 1;
            return is_var_in_term(var,APP_ARG(term,1));

    }
}

/* Sets a flag to on or off. */
extern void set_flag(store_s *store,word_t flag,word_t on)
{
    if(on)
        store->flags |= flag;
    else 
        store->flags &= ~flag;
}

/*****************************************************************************/
/* Implementation of the global symbol table.                                */
/*****************************************************************************/

static unsigned hash_symbol(const char *symbol)
{
    unsigned hval = 0, i;
    for (i = 0; symbol[i]; i++) {
            hval = 31*hval + symbol[i];
    }
    return hval;
}

static bucket_s *make_new_bucket(const char *symbol)
{
    bucket_s *bucket = (bucket_s *)malloc(sizeof(bucket_s));
    bucket->symbol = strdup(symbol);
    bucket->next   = NULL;
    return bucket;
}

static word_t get_symbol_code(const char *symbol) 
{
    bucket_s *curr, *prev;
    unsigned hval, count;

#ifdef HERBIE_DEBUG
    fprintf(stderr,"herbie: get_symbol_code(\"%s\") = ",symbol);
#endif
    
    hval = hash_symbol(symbol) % SYMBOL_TABLE_SIZE;
    if(table[hval] == NULL) {
        table[hval] = make_new_bucket(symbol);
#ifdef HERBIE_DEBUG
        fprintf(stderr,"%d\n",SYMBOL_CODE(hval,0));
#endif
        return SYMBOL_CODE(hval,0);
    } else {
        curr = table[hval];
        prev = NULL;
        count = 0;
        while(curr != NULL) {
            if(strcmp(symbol,curr->symbol) == 0) {
#ifdef HERBIE_DEBUG
                fprintf(stderr,"%d\n",SYMBOL_CODE(hval,count));
#endif
                return SYMBOL_CODE(hval,count);
            }
            prev = curr;
            curr = curr->next;
            count++;
            if(count > MAX_CHAIN_SIZE) {
                fprintf(stderr,"herbie: (BUG) symbol table full.\n");
                exit(EXIT_FAILURE);
            }
        }
        prev->next = make_new_bucket(symbol);
#ifdef HERBIE_DEBUG
        fprintf(stderr,"%d\n",SYMBOL_CODE(hval,count));
#endif
        return SYMBOL_CODE(hval,count);
    }
}

extern char *get_code_symbol(word_t *code)
{
    bucket_s *bucket;
    unsigned hval, count;
    
    DEREF(code);
    hval  = GET_HASHVAL((word_t)code);
    count = GET_COUNT((word_t)code);

    bucket = table[hval];
    while(count != 0) {
        bucket = bucket->next;
        count--;
    }
    return bucket->symbol; 
}

#ifdef HERBIE_DEBUG
static void debug_unify(const char *fn,char c,word_t *term1,word_t *term2)
{
    fprintf(stderr,"herbie: %s(",fn);
    print_term_rec(term1,stderr);
    putc(',',stderr);
    print_term_rec(term2,stderr);
    fprintf(stderr,")%c",c);
}
#endif
