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

team_t team = {
        /* Team name */
        "jungle_week6_team07",
        /* First member's full name */
        "youngdong kim",
        /* First member's email address */
        "zeroistfilm@naver.com",
        /* Second member's full name (leave blank if none) */
        "",
        /* Second member's email address (leave blank if none) */
        ""
};

#define ALIGNMENT 8
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT -1)) & ~0x7)
#define SIZEMASK (~0x7)
#define PACK(size, alloc) ((size) | (alloc))
#define getSize(x) ((x)->size & SIZEMASK)
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE 1<<10
#define MINIMUM 24
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define GET(p) (*(int *)(p))
#define PUT(p, val) (*(int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(HDRP(bp) - WSIZE))
#define NEXT_FREEP(bp) (*(void **)(bp + DSIZE))
#define PREV_FREEP(bp) (*(void **)(bp))
static char *heap_listp = 0;
static char *free_listp = 0;
static char *next_bp =0;

static void *extendHeap(size_t words);

static void place(void *bp, size_t asize);

static void *findFit(size_t asize);

static void *coalesce(void *bp);

static void removeBlock(void *bp);


int mm_init(void) {
    if ((heap_listp = mem_sbrk(2 * MINIMUM)) == NULL)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(MINIMUM, 1));
    PUT(heap_listp + DSIZE, 0);
    PUT(heap_listp + DSIZE + WSIZE, 0);
    PUT(heap_listp + MINIMUM, PACK(MINIMUM, 1));
    PUT(heap_listp + WSIZE + MINIMUM, PACK(0, 1));
    free_listp = heap_listp + DSIZE;
    next_bp =free_listp;
    if (extendHeap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;
    if (size <= 0)
        return NULL;
    asize = MAX(ALIGN(size) + DSIZE, MINIMUM);
    if (bp = findFit(asize)) {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extendHeap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp) {
    if (!bp) return;
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *) ((char *) oldptr - WSIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}


static void removeBlock(void *bp) {
    if (PREV_FREEP(bp))
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
    else
        free_listp = NEXT_FREEP(bp);
    PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
}

static void *findFit(size_t asize) {
    void *bp;
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
        if (asize <= (size_t) GET_SIZE(HDRP(bp)))
            return bp;
    }
//    for (bp = free_listp; bp != next_bp; bp = NEXT_BLKP(bp)) {
//        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//            return bp;
//        }
//    }

    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= MINIMUM) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        removeBlock(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        removeBlock(bp);
    }
}

static void *extendHeap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (size < MINIMUM)
        size = MINIMUM;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        removeBlock(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        removeBlock(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    NEXT_FREEP(bp) = free_listp;
    PREV_FREEP(free_listp) = bp;
    PREV_FREEP(bp) = NULL;
    free_listp = bp;
    next_bp =bp;
    return bp;

}