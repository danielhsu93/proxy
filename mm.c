#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Daniel/Victoria",
	/* First member's full name */
	"Daniel Hsu",
	/* First member's email address */
	"dh15@rice.edu",
	/* Second member's full name (leave blank if none) */
	"Te-Rue Victoria Eng",
	/* Second member's email address (leave blank if none) */
	"tve1@rice.edu"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define SEGLIST1 ((char *) (heap_listp - 26 * DSIZE))
#define SEGLIST2 ((char *) (heap_listp - 24 * DSIZE))
#define SEGLIST3 ((char *) (heap_listp - 22 * DSIZE))
#define SEGLIST4 ((char *) (heap_listp - 20 * DSIZE))	
#define SEGLIST5 ((char *) (heap_listp - 18 * DSIZE))
#define SEGLIST6 ((char *) (heap_listp - 16 * DSIZE))	
#define SEGLIST7 ((char *) (heap_listp - 14 * DSIZE))				
#define SEGLIST8 ((char *) (heap_listp - 12 * DSIZE))
#define SEGLIST9 ((char *) (heap_listp - 10 * DSIZE))
#define SEGLIST10 ((char *) (heap_listp - 8 * DSIZE))
#define SEGLIST11 ((char *) (heap_listp - 6 * DSIZE))
#define SEGLIST12 ((char *) (heap_listp - 4 * DSIZE))
#define SEGLIST13 ((char *) (heap_listp - 2 * DSIZE))
#define SEGLIST14 ((char *) (heap_listp))
#define LISTSIZE 14

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(WSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Address of pointer to the next and previous free blocks. */
#define NEXTFREEP(bp) ((char *)(bp)) 
#define PREVFREEP(bp) ((char *)(bp) + WSIZE) 

/* Address of next and previous free blocks. */
#define NEXTFREEPB(bp) ((char *)GET(NEXTFREEP(bp)))
#define PREVFREEPB(bp) ((char *)GET(PREVFREEP(bp)))

static char *heap_listp;

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *get_bound(size_t asize);
static void addtolist(void *headp, void *bp);
static void removefromlist(void *bp);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* 
 * Effects:
 * 		gets the appropriate bucket to put block in.
 */ 
static void*
get_bound(size_t asize) 
{
	if (asize <= 0)
		return NULL;
 	if (asize < 64) {
 		return SEGLIST1;
 	} else if (asize < 128) {
 		return SEGLIST2;
 	} else if (asize < 256) {
 		return SEGLIST3;
 	} else if (asize < 512) {
 		return SEGLIST4;
 	} else if (asize < 1024) {
 		return SEGLIST5;
 	} else if (asize < 2048) {
 		return SEGLIST6;
 	} else if (asize < 4096) {
 		return SEGLIST7;
 	} else if (asize < 8192) {
 		return SEGLIST8;
 	} else if (asize < 16384){
 		return SEGLIST9;
 	} else if (asize < 32768){
 		return SEGLIST10;
 	} else if (asize < 65536){
 		return SEGLIST11;
 	} else if (asize < 131072){
 		return SEGLIST12;
 	} else if (asize < 262144){
 		return SEGLIST13;
 	} else {
 		return SEGLIST14;
 	}
 }
/* Requires:
 *		headp, bp : the address of a block
 * Effects:
 * 		adds the block to list.
 */ 
static void 
addtolist(void *headp, void *bp) 
{
 	if (PREVFREEPB(SEGLIST1) == heap_listp){ 
 		/* No free block available */
 		if (heap_listp == headp) {
 			PUT(PREVFREEP(SEGLIST1), (uintptr_t) (bp));		
		} 
		else {
			PUT(PREVFREEP(NEXTFREEPB(headp)), (uintptr_t) bp);
		}
		PUT(PREVFREEP(bp), (uintptr_t) headp);
 		PUT(NEXTFREEP(bp), (uintptr_t) (NEXTFREEPB(headp)));
		PUT(NEXTFREEP(headp), (uintptr_t) bp);
	} 
	else {
 		PUT(NEXTFREEP(bp), (uintptr_t) (NEXTFREEPB(headp)));
		PUT(PREVFREEP(bp), (uintptr_t) headp);
		PUT(NEXTFREEP(headp), (uintptr_t) bp);
		PUT(PREVFREEP(NEXTFREEPB(bp)), (uintptr_t) bp);
	}
}

/* Required:
 * 		"bp" is address of a block.
 * Effects:
 * 		Remove the block from seg list.
 */
static void
removefromlist(void *bp) 
{
	if (GET_SIZE(HDRP(NEXTFREEPB(bp)))){
		PUT(NEXTFREEP(PREVFREEPB(bp)), (uintptr_t) NEXTFREEPB(bp));
		PUT(PREVFREEP(NEXTFREEPB(bp)), (uintptr_t) PREVFREEPB(bp));
	} 
	else {
		PUT(NEXTFREEP(PREVFREEPB(bp)), (uintptr_t) (mem_heap_hi() + 1));
		PUT(PREVFREEP(SEGLIST1), (uintptr_t) PREVFREEPB(bp));
	}
}


/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
 
int
mm_init(void) 
{
	int i;
	if ((heap_listp = mem_sbrk((4 * LISTSIZE + 1) * WSIZE)) == (void *)-1)
		return (-1);	
	
	//PUT(PREVFREEP(heap_listp + WSIZE), (uintptr_t)(heap_listp + WSIZE));
	for (i=0;i < LISTSIZE; i++) {
		//PUT(heap_listp, 0);  					/* Alignment padding */
		PUT(heap_listp, PACK(4 * WSIZE, 1)); /* Prologue header */
		PUT(heap_listp + (3 * WSIZE), PACK(4 * WSIZE, 1)); /* Prologue footer */
		PUT(NEXTFREEP(heap_listp + WSIZE), (uintptr_t)NEXT_BLKP(heap_listp + WSIZE)); 
		PUT(PREVFREEP(heap_listp + WSIZE), (uintptr_t)(heap_listp - 3 * WSIZE));
		heap_listp += (4 * WSIZE);
	}

	PUT(heap_listp, PACK(0, 1));
	heap_listp += -(3 * WSIZE);
	PUT(PREVFREEP(SEGLIST1), (uintptr_t) heap_listp);
	
	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1); 
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= WSIZE)
		asize = 2 * DSIZE;
	else
		asize = WSIZE * ((size + DSIZE + (WSIZE - 1)) / WSIZE);
		
	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = asize + DSIZE;
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void*
mm_realloc(void *ptr, size_t size)
{
	size_t asize;
	size_t oldsize;
	size_t csize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));
	
	if (size <= WSIZE)
		asize = DSIZE + DSIZE;
	else
		asize = WSIZE * ((size + DSIZE + (WSIZE - 1)) / WSIZE);
		
	oldsize = GET_SIZE(HDRP(ptr));
	if (oldsize <= asize) {
		bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
		csize = oldsize;
		/* combine available free blocks. */
		if (!next_alloc) {
			csize += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
			if (csize >= ((4 * WSIZE) + asize)) {
				removefromlist(NEXT_BLKP(ptr));
				PUT(HDRP(ptr), PACK(asize, 1));
				PUT(FTRP(ptr), PACK(asize, 1));
				PUT(HDRP(NEXT_BLKP(ptr)), PACK(csize - asize, 0));
				PUT(FTRP(NEXT_BLKP(ptr)), PACK(csize - asize, 0));
				addtolist(get_bound(csize - asize), NEXT_BLKP(ptr));				
				return ptr;
			}
		}	
	} 
	if (oldsize > asize + (4 * WSIZE)) {
		place(ptr,asize);
		return ptr;
	}
	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		addtolist(get_bound(size), bp);
		return (bp);		
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		removefromlist(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		addtolist(get_bound(size), bp);
		return (bp);
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		removefromlist(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		addtolist(get_bound(size), PREV_BLKP(bp));
		return PREV_BLKP(bp);
	} else {                                        /* Case 4 */
		removefromlist(NEXT_BLKP(bp));
		removefromlist(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		addtolist(get_bound(size), PREV_BLKP(bp));
		return PREV_BLKP(bp);
	}
	return NULL;
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);
	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	/* Handle epilogue pointer */
	PUT(NEXTFREEP(PREVFREEPB(SEGLIST1)), (uintptr_t) NEXT_BLKP(bp));

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
	void *bp;

	/* Search for the first fit. */
	for (bp = get_bound(asize); GET_SIZE(HDRP(bp)) > 0; bp = NEXTFREEPB(bp)){
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
			return (bp);
	}
	/* No fit was found. */
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2 * DSIZE)) {
		removefromlist(bp); 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		addtolist(get_bound(csize-asize), bp);
	} 
	else {
		removefromlist(bp);
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % WSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;
	
	if (verbose)
		printf("Heap (%p):\n", heap_listp);
		
	if (GET_SIZE(HDRP(heap_listp)) != 2*DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
			printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = SEGLIST1; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;


	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp)); 

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'),  
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
