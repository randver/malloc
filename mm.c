/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 * 
 * Note: This assignment is a _baseline_ for the performance grade.
 * You will need to exceed the performance of this implicit first-fit placement
 * (which is about 54/100).
 */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

/* Team structure */
team_t team = {
    /* Group name */
    "TeamDeadline",
    /* First member's full name */
    "Randver Palmi Gyduson",
    /* First member's email address */
    "randver10@ru.is",
    /* Second member's full name (leave blank if none) */
    "Eirikur Bjorn Einarsson",
    /* Second member's email address (leave blank if none) */
    "eirikurbe10@ru.is",
    /* Leave blank */
    "",
    /* Leave blank */
    ""
};
/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE 4 /* word size (bytes) */
#define DSIZE 8 /* doubleword size (bytes) */
#define CHUNKSIZE (1<<12) /* initial heap size (bytes) */
#define OVERHEAD 8 /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Additional constants and macros */

#define RIGHT(bp) ((void *)* (int *)(bp+WSIZE))
#define LEFT(bp) ((void *)* (int *)(bp))
#define SETLEFT(bp, bq) (*(int *)(bp)) = (int)(bq)
#define SETRIGHT(bp, bq) (*(int *)(bp+WSIZE)) = (int)(bq)
#define GETSIZE(bp) ((*(int*) (bp-WSIZE)) & ~7)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val)) //store val where p is pointing to

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

/* The only global variable is a pointer to the first block */
static char *heap_listp;
static void *tree_root;

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);

/* Additional function declarations */
void *mm_insert(void *root, void *bp);
void *mm_remove(void *root, void *bp);
void *mm_fitter(void *root, int size);
void *mm_parent(void *root, void *bp);
void *mm_replace(void *bp);


int mm_children(void *root);

/*
* mm_init - Initialize the memory manager
*/
/* $begin mminit */
int mm_init(void)
{
    void *bp;

    tree_root = NULL;

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
        return -1;

    PUT(heap_listp, 0); /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1)); /* prologue header */
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1)); /* prologue footer */
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1)); /* epilogue header */
    heap_listp += DSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    bp = extend_heap(CHUNKSIZE/WSIZE);

    if (bp == NULL)
        return -1;

    tree_root = mm_insert(tree_root, bp);

    return 0;
}
/* $end mminit */

/*
* mm_malloc - Allocate a block with at least size bytes of payload
*/
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
    size_t asize; /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = DSIZE + OVERHEAD;
    else
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    
    /* Search the free list for a fit */
    if ((bp = mm_fitter(tree_root,asize)) != NULL)
    {
        tree_root = mm_remove(tree_root,bp);
        bp = place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);

    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    bp = place(bp, asize);

    return bp;
}
/* $end mmmalloc */

/*
* mm_free - Free a block
*/
/* $begin mmfree */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    tree_root = mm_insert(tree_root,coalesce(bp));
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
    printf("ERROR: mm_malloc failed in mm_realloc\n");
    exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
      copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/*
* mm_checkheap - Check the heap for consistency
*/
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
    printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose) 
        printblock(bp);
    checkblock(bp);
    }
     
    if (verbose)
    printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
    printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/*
* extend_heap - Extend heap with free block and return its block pointer
*/
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((int)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/*
* place - Place block of asize bytes at start of free block bp
* and split if remainder would be at least minimum block size
*/
/* $begin mmplace */
/* $begin mmplace-proto */
static void *place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));   
/* we have no idea what we are doing here. Randi wrote the first splitter
   Eyky wrote the second splitter, they got us diffrent resaults so we just used
   them both*/
    if ((csize - asize) >= (6*OVERHEAD)) { 
       if(GETSIZE(NEXT_BLKP(bp)) > GETSIZE(PREV_BLKP(bp))) {
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            void* blah = NEXT_BLKP(bp);
            PUT(HDRP(blah), PACK(csize-asize, 0));
            PUT(FTRP(blah), PACK(csize-asize, 0));
            tree_root = mm_insert(tree_root,blah);
            return bp;
        }
        else{
            PUT(HDRP(bp), PACK(csize-asize, 0));
            PUT(FTRP(bp), PACK(csize-asize, 0));
            void* blah = NEXT_BLKP(bp);
            PUT(HDRP(blah), PACK(asize, 1));
            PUT(FTRP(blah), PACK(asize, 1));
            tree_root = mm_insert(tree_root,bp);
            return blah;

        }
    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        return bp;
    }

}
/* $end mmplace */



/*
* coalesce - boundary tag coalescing. Return ptr to coalesced block
*/
/* $begin mmfree */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
    return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    tree_root = mm_remove(tree_root, NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size,0));

    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    tree_root = mm_remove(tree_root, PREV_BLKP(bp));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);


    }

    else {                                     /* Case 4 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
    tree_root = mm_remove(tree_root, NEXT_BLKP(bp));
    tree_root = mm_remove(tree_root, PREV_BLKP(bp));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
    }

    return bp;
}


static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
       hsize, (halloc ? 'a' : 'f'), 
       fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/*
* mm_insert - Insert a free block into the Binary Tree and return bp
*/
void *mm_insert(void *root, void* bp){

    if(root == NULL){
        SETLEFT(bp, NULL);
        SETRIGHT(bp, NULL);
        return bp;
    }
    else if(GETSIZE(bp) <= GETSIZE(root)){
        SETLEFT(root, mm_insert(LEFT(root), bp));
        return root;
    }
    else{
        SETRIGHT(root, mm_insert(RIGHT(root), bp));
        return root;
    }
}

/*
* mm_remove - Remove a node from the Binary Tree
*/
void *mm_remove(void *root, void *bp)
{
    /* Determine if there are any children, if not, remove the node */

    if(mm_children(bp) == 0) {
        void *parent_node = mm_parent(root, bp);
    
        if(parent_node != NULL)
        {
            if(LEFT(parent_node) == bp)
                SETLEFT(parent_node, NULL);
            else
                SETRIGHT(parent_node, NULL);
            return root;
        }
        else
        {
            return NULL;
        }
    }
    /* If there is a child, find it, and move it up */
    else if(mm_children(bp) == 1) {
        void *parent_node = mm_parent(root, bp);
        void *child;
     
        if(LEFT(bp) != NULL)
            child = LEFT(bp);
        else
            child = RIGHT(bp);

        if(parent_node != NULL)
        {
            if(LEFT(parent_node) == bp)
                SETLEFT(parent_node, child);
            else
                SETRIGHT(parent_node, child);
            return root;
        }
        else
        {
            return child;
        }
    }
    else {
        void *parent_node = mm_parent(root, bp);
        void *replacement = mm_replace(LEFT(bp));
        void *new_bp;
     
        /* Remove the replacement and store the new bp */

        new_bp = mm_remove(LEFT(bp), replacement);
     
        SETLEFT(replacement, new_bp);
        SETRIGHT(replacement, RIGHT(bp));
     
        if(parent_node != NULL)
        {
            if(LEFT(parent_node) == bp)
                SETLEFT(parent_node, replacement);
            else
                SETRIGHT(parent_node, replacement);
            return root;
        }
        else
        {
            return replacement;
        }
    }
}



/*
* mm_fitter - Locate a node that best fits in a free block and return its pointer
*/
void *mm_fitter(void* root, int size){


    if(root == NULL){ 

        return NULL;   
    }
    if(GETSIZE(root) >= size){
        return root;
    }

    else if(GETSIZE(root) < size){
        return mm_fitter(RIGHT(root), size);
    }    
    
}


/*
* mm_parent - Retrieve the parent node of a child node
*/
void *mm_parent(void *root, void *bp)
{
    if(bp == root)
        return NULL;

    if(GETSIZE(bp) <= GETSIZE(root))
    {
        if(LEFT(root) == bp)
            return root;
        else
            return mm_parent(LEFT(root),bp);
    }
    else
    {
        if(RIGHT(root) == bp)
            return root;
        else
            return mm_parent(RIGHT(root),bp);
    }
}

/*
* mm_children - Return the number of children under a given root node
*/
int mm_children(void *root)
{
    int child_num = 0;

    /* Do we have any children on either side? */

    if(LEFT(root) != NULL)
         child_num++;
    if(RIGHT(root) != NULL)
         child_num++;
                            
    return child_num;
}

/*
* mm_replace - Locate the replacement for the parents' two children
*/
void *mm_replace(void *bp)
{
     if(RIGHT(bp) == NULL)
        return bp;
     else
        return mm_replace(RIGHT(bp));
}