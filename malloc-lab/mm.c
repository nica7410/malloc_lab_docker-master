/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MIN_BLOCK_SIZE 24   // Header 4, PRED 8, SUCC 8, Footer 4
#define WSIZE       4
#define DSIZE       8
#define CHUNKSIZE   (1 << 12)
#define MAX(x, y)   ((x) > (y) ? (x) : (y))
#define PACK(size, alloc)  ((size) | (alloc))
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, value)     (*(unsigned int *)(p) = (value))
#define GET_SIZE(p)       (GET(p) & ~0x7)
#define GET_ALLOC(p)      (GET(p) & 0x1)
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

static char *heap_listp;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_free_block(void *bp);
static void remove_free_block(void *bp);

static void *free_list_head = NULL;
/* 이전 free block 주소 */
#define PRED(bp) (*(void **)(bp))
/* 다음 free block 주소 */
#define SUCC(bp) (*(void **)((char *)(bp) + sizeof(void *)))

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    free_list_head = NULL;
    heap_listp = mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *)-1)
        return -1;

    PUT(heap_listp,             0);               /* 정렬용 */
    PUT(heap_listp + WSIZE,     PACK(DSIZE, 1));  /* 프롤로그 헤더 */
    PUT(heap_listp + DSIZE, PACK(DSIZE, 1));  /* 프롤로그 풋터 */
    PUT(heap_listp + WSIZE + DSIZE, PACK(0, 1));      /* 에필로그 헤더 */
    heap_listp += DSIZE;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}
static void *extend_heap(size_t words)
{
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    char *bp = mem_sbrk(size);
    if (bp == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) return NULL;

    asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    if (asize < MIN_BLOCK_SIZE) asize = MIN_BLOCK_SIZE;

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;

    copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if (size < copySize) copySize = size;

    memcpy(newptr, ptr, copySize);
    mm_free(ptr);

    return newptr;
}


// 1. [할당][free][할당]
//       → 합칠 것 없음
// 2. [할당][free][free]
//       → 현재 + 다음
// 3. [free][free][할당]
//       → 이전 + 현재
// 4. [free][free][free]
//       → 이전 + 현재 + 다음
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {              /* 경우 1 */
    }
    else if (prev_alloc && !next_alloc) {        /* 경우 2 */
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {        /* 경우 3 */
        void *prev_bp = PREV_BLKP(bp);
        remove_free_block(prev_bp);
        size += GET_SIZE(HDRP(prev_bp));
        PUT(HDRP(prev_bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = prev_bp;
    }
    else {                                      /* 경우 4 */
        void *prev_bp = PREV_BLKP(bp);
        void *next_bp = NEXT_BLKP(bp);
        remove_free_block(prev_bp);
        remove_free_block(next_bp);

        size += GET_SIZE(HDRP(prev_bp))
              + GET_SIZE(HDRP(next_bp));

        PUT(HDRP(prev_bp), PACK(size, 0));
        PUT(FTRP(next_bp), PACK(size, 0));
        bp = prev_bp;
    }
    insert_free_block(bp);
    return bp;
}

static void *find_fit(size_t asize)
{    
    for (void *bp = free_list_head;
         bp != NULL;
         bp = SUCC(bp)) 
    {
        if (asize <= GET_SIZE(HDRP(bp))) return bp;
    }
    return NULL;
}
static void place(void *bp, size_t asize)
{
    remove_free_block(bp);
    size_t csize = GET_SIZE(HDRP(bp));
    if (csize - asize >= MIN_BLOCK_SIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        insert_free_block(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void insert_free_block(void *bp)
{
    PRED(bp) = NULL;
    SUCC(bp) = free_list_head;

    if (free_list_head != NULL) PRED(free_list_head) = bp;

    free_list_head = bp;
}

static void remove_free_block(void *bp)
{
    void *pred = PRED(bp);
    void *succ = SUCC(bp);

    if (pred != NULL) SUCC(pred) = succ;
    else free_list_head = succ;

    if (succ != NULL) PRED(succ) = pred;    
}