/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply in
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
    "Swjungle-2",
    /* First member's full name */
    "Lee Jinho",
    /* First member's email address */
    "jinho605@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// Basic constants and macros
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define INITCHUNKSIZE (1<<6)
#define LISTLIMIT 20
#define REALLOC_BUFFER (1<<7)


// calculate max value
#define MAX(x,y) ((x)>(y) ? (x) : (y))
#define MIN(x,y) ((x)<(y) ? (x) : (y))

//size와 할당 여부를 하나로 합친다
#define PACK(size,alloc) ((size)|(alloc))

//포인터 p가 가르키는 주소의 값을 가져온다.
#define GET(p) (*(unsigned int *)(p))

// Read the size and allocation bit from address p 
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p)   (GET(p) & 0x2)
#define SET_RATAG(p)   (GET(p) |= 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)

//포인터 p가 가르키는 곳에 val을 역참조로 갱신
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))

//블럭포인터를 통해 헤더 포인터,푸터 포인터 계산
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//블럭포인터 -> 블럭포인터 - WSIZE : 헤더위치 -> GET_SIZE으로 현재 블럭사이즈계산 -> 다음 블럭포인터 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
//블럭포인터 -> 블럭포인터 - DSIZE : 이전 블럭 푸터 -> GET_SIZE으로 이전 블럭사이즈계산 -> 이전 블럭포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//포인터 p가 가르키는 메모리에 포인터 ptr을 입력
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

//가용 블럭 리스트에서 next 와 prev의 포인터를 반환
#define NEXT_PTR(ptr) ((char *)(ptr))
#define PREV_PTR(ptr) ((char *)(ptr) + WSIZE)

//segregated list 내에서 next 와 prev의 포인터를 반환
#define NEXT(ptr) (*(char **)(ptr))
#define PREV(ptr) (*(char **)(PREV_PTR(ptr)))

//전역변수 
char *heap_listp;
void *segregated_free_lists[LISTLIMIT];

//함수 목록
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int list;
    
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    /* Create the initial empty heap */
    if ((long)(heap_listp = mem_sbrk(4*WSIZE)) == -1)
        return -1;
    
    PUT_NOTAG(heap_listp, 0);                          /* Alignment padding */
    PUT_NOTAG(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;  
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = ALIGN(words);
    
    if((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    PUT_NOTAG(HDRP(bp),PACK(size,0));
    PUT_NOTAG(FTRP(bp),PACK(size,0));
    PUT_NOTAG(HDRP(NEXT_BLKP(bp)),PACK(0,1));
    insert_node(bp,size);

    return coalesce(bp);
}

static void insert_node(void *ptr, size_t size) {
    int list = 0;
    void *search_ptr = ptr; 
    void *insert_ptr = NULL; //실제 노드가 삽입되는 위치
    
    // Select segregated list 
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    // Keep size ascending order and search
    search_ptr = segregated_free_lists[list];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = NEXT(search_ptr);
    }
    
    // Set NEXT and PREV 
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(NEXT_PTR(ptr), search_ptr);
            SET_PTR(PREV_PTR(search_ptr), ptr);
            SET_PTR(PREV_PTR(ptr), insert_ptr);
            SET_PTR(NEXT_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(NEXT_PTR(ptr), search_ptr);
            SET_PTR(PREV_PTR(search_ptr), ptr);
            SET_PTR(PREV_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    } else {
        if (insert_ptr != NULL) {
            SET_PTR(NEXT_PTR(ptr), NULL);
            SET_PTR(PREV_PTR(ptr), insert_ptr);
            SET_PTR(NEXT_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(NEXT_PTR(ptr), NULL);
            SET_PTR(PREV_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    }
    
    return;
}

static void delete_node(void *ptr) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));
    
    // Select segregated list 
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    if (NEXT(ptr) != NULL) {
        if (PREV(ptr) != NULL) {
            SET_PTR(PREV_PTR(NEXT(ptr)), PREV(ptr));
            SET_PTR(NEXT_PTR(PREV(ptr)), NEXT(ptr));
        } else {
            SET_PTR(PREV_PTR(NEXT(ptr)), NULL);
            segregated_free_lists[list] = NEXT(ptr);
        }
    } else {
        if (PREV(ptr) != NULL) {
            SET_PTR(NEXT_PTR(PREV(ptr)), NULL);
        } else {
            segregated_free_lists[list] = NULL;
        }
    }
    
    return;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize;
    size_t extendsize; //들어갈 자리가 없을때 늘려야 하는 힙의 용량
    
    char *bp;

    /* Ignore spurious*/
    if (size == 0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        // asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
        asize = ALIGN(size + DSIZE);
    
    bp = find_fit(asize);
    
    // if free block is not found, extend the heap
    if (bp == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((bp = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    // Place and divide block
    bp = place(bp, asize);


    return bp;
}

//전,후에 free block 이 있을시 합쳐줌 + 합쳐지는 경우 segregation_lists에서 기존 free block 노드 삭제해줌
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    
    if (GET_TAG(HDRP(PREV_BLKP(bp))))
        prev_alloc = 1;
    
    if(prev_alloc && next_alloc){
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        delete_node(bp);
        delete_node(NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    else if (!prev_alloc && next_alloc){
        delete_node(bp);
        delete_node(PREV_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else{
        delete_node(bp);
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    
    insert_node(bp,size);
    return bp;
}

static void *find_fit(size_t asize){
    char *bp; 
    
    int list = 0; 
    size_t searchsize = asize;
    // Search for free block in segregated list
    while (list < LISTLIMIT) {
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            bp = segregated_free_lists[list];
            // Ignore blocks that are too small or marked with the reallocation bit
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp))) || (GET_TAG(HDRP(bp)))))
            {
                bp = NEXT(bp);
            }
            if (bp != NULL)
                return bp;
        }
        
        searchsize >>= 1;
        list++;
    }

    return NULL;
}

static void *place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remainder = csize - asize;
    delete_node(bp);

    if (remainder <= 2*DSIZE){
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
    else if(asize >= 100){
        PUT(HDRP(bp),PACK(remainder,0));
        PUT(FTRP(bp),PACK(remainder,0));
        PUT_NOTAG(HDRP(NEXT_BLKP(bp)),PACK(asize,1));
        PUT_NOTAG(FTRP(NEXT_BLKP(bp)),PACK(asize,1));
        insert_node(bp,remainder);
        return NEXT_BLKP(bp);
    }
    else{
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        PUT_NOTAG(HDRP(NEXT_BLKP(bp)),PACK(remainder,0));
        PUT_NOTAG(FTRP(NEXT_BLKP(bp)),PACK(remainder,0));
        insert_node(NEXT_BLKP(bp),remainder);
    }
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    REMOVE_RATAG(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    
    insert_node(bp,size);

    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;
    
//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//       return NULL;
//     // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     copySize = GET_SIZE(HDRP(oldptr));
//     if (size < copySize)
//       copySize = size;
//     memcpy(newptr, oldptr, copySize);
//     mm_free(oldptr);
//     return newptr;
// }
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */
    
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    // Align block size
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }
    
    /* Add overhead requirements to block size */
    new_size += REALLOC_BUFFER;
    
    /* Calculate block buffer */
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size;
    
    /* Allocate more space if overhead falls below the minimum */
    if (block_buffer < 0) {
        /* Check if next block is a free block or the epilogue block */
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }
            
            delete_node(NEXT_BLKP(ptr));
            
            // Do not split block
            PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1)); 
            PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1));  
        } else {
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }
        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }
    
    // Tag the next block if block overhead drops below twice the overhead 
    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));
    
    // Return the reallocated block 
    return new_ptr;
}