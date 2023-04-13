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

/* Basic constants and macros */
#define WSIZE 4             /* Wor and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합해서 헤더와 풋터 저장할 값을 리턴

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))              // p가 참조하는 워드를 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p가 가리키는 워드에 val을 저장

/* Read the size and allocated fields from address p */
// & ~0x7 => 0x7:0000 0111 ~0x7:1111 1000이므로 ex. 1011 0111 & 1111 1000 = 1011 0000 : size 176bytes
// & 0x1 => ex. 1011 0111 | 0000 0001 = 1 : Allocated!
#define GET_SIZE(p) (GET(p) & ~0x7) // 헤더 or 풋터의 size return
#define GET_ALLOC(p) (GET(p) & 0x1) // 헤더 or 풋터의 할당비트 return

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)                        // 헤더를 가리키는 포인터 리턴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 풋터를 가리키는 포인터 리턴

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 내 head에서 size를 얻어 bp 에서 더하기
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 워드의 footer에서 size를 얻어서 bp에서 빼기

#define PREV_LINK(bp) (*(char **)(bp))         // prev 포인터 위치
#define NEXT_LINK(bp) (*(char **)(bp + WSIZE)) // next 포인터 위치

#define LIST_NUM 32
// 블록 최소 크기인 2**4부터 최대 크기인 2**32를 위한 리스트 unsigned int 의 최댓값
// 32비트 아키텍처에서 주소 공간의 크기는 2^32바이트 또는 4GB입니다.

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void add_free_block(void *bp);
static void remove_free_block(void *bp);

static char *heap_listp;          // 항상 prologue block 을 가리키는 변수
static void *free_list[LIST_NUM]; // 분리 가용 리스트 관리

/*
 *mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    for (int i = 0; i < LIST_NUM; i++)
    {
        free_list[i] = NULL;
    }
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // 메모리에서 4word 가져와서 빈 가용 리스트 초기화
        return -1;
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);                     // 항상 prologue block을 가리킴

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}
/*
 *extend_heap - 힙 늘려주기
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : (words)*WSIZE; // size를 짝수로 맞춰줌
    if ((long)(bp = mem_sbrk(size)) == -1)                    // 추가적인 힙 공간 요청
        return NULL;
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static int find_index(size_t asize)
{
    int index;
    for (index = 0; index < LIST_NUM; index++)
    {
        if ((1 << index) >= asize)
        {
            return index;
        }
    }
    return index;
}

static void add_free_block(void *bp)
{
    int index = find_index(GET_SIZE(HDRP(bp)));

    // 맨 처음 삽입한다면
    if (free_list[index] == NULL)
    {
        NEXT_LINK(bp) = NULL;
        PREV_LINK(bp) = NULL;
        free_list[index] = bp;
    }
    else
    {
        PREV_LINK(bp) = NULL;
        NEXT_LINK(bp) = free_list[index];
        PREV_LINK(free_list[index]) = bp;
        free_list[index] = bp;
    }
}
static void remove_free_block(void *bp)
{
    int index = find_index(GET_SIZE(HDRP(bp)));
    // 맨 앞이 아닌 블록을 삭제하는 경우
    if (free_list[index] != bp)
    {
        // 맨 뒤가 아닌 블록(중간인 블록)
        if (NEXT_LINK(bp) != NULL)
        {
            PREV_LINK(NEXT_LINK(bp)) = PREV_LINK(bp);
            NEXT_LINK(PREV_LINK(bp)) = NEXT_LINK(bp);
        }
        // 맨 뒤 블록
        else
        {
            NEXT_LINK(PREV_LINK(bp)) = NULL;
        }
    }
    // 맨 앞 블록인 경우
    else
    {
        // bp 다음 블록이 있는 경우
        if (NEXT_LINK(bp) != NULL)
        {
            PREV_LINK(NEXT_LINK(bp)) = NULL;
            free_list[index] = NEXT_LINK(bp);
        }
        // 혼자인 경우
        else
        {
            free_list[index] = NULL;
        }
    }
}

/*
 *mm_free - Freeing a block does nothing
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // block size 가져오기

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 앞 뒤가 가용이면 연결
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 가용 없음
    if (prev_alloc && next_alloc)
    {
        add_free_block(bp);
        return bp;
    }
    // case 2 뒤만 가용
    else if (prev_alloc && !next_alloc)
    {
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0)); // footer 찾아올 때 head의 사이즈를 가지고 찾아오기 때문에 case 4와 다르게 작성
    }
    // case 3 앞만 가용
    else if (!prev_alloc && next_alloc)
    {
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // case 4 앞 뒤 가용
    else
    {
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // bp는 움직이지 않았고 헤드에 있는 사이즈가 달라졌기 때문에 넥스트에서 찾음 // NEXT_BLKP 부분을 PREV_BLKP로 바꿔도 됨
        bp = PREV_BLKP(bp);
    }
    add_free_block(bp);
    return bp;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    // 맞는 블록 찾으면 할당 하고 분할
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    // 맞는 가용 블록이 없다면 힙을 늘리기
    extendsize = MAX(asize, CHUNKSIZE);
    // extend_heap 은 word 단위로 인자를 받으므로 WSIZE로 나눠준다.
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{
    int index = find_index(asize);
    void *bp;

    for (int i = index; i < LIST_NUM; i++)
    {
        bp = free_list[i];
        while (bp != NULL)
        {
            if (GET_SIZE(HDRP(bp)) >= asize)
                return bp;
            bp = NEXT_LINK(bp);
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 이전 블록의 크기를 가져옴
    remove_free_block(bp);

    // 블록 내부의 여유 공간이 충분한 경우
    if ((csize - asize) >= (2 * DSIZE))
    {
        // 블록을 분할하고, 새 블록의 헤더와 푸터를 설정
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    }
    // 블록 내부의 여유 공간이 충분하지 않은 경우
    else
    {
        // 블록 전체를 사용하고, 헤더와 푸터를 설정
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; // 이전 메모리 블록의 포인터를 oldptr 변수에 저장
    void *newptr;
    size_t copySize; // 복사해야 하는 데이터 크기를 저장하는 변수

    // 새로운 메모리 블록을 요청한 크기로 할당하고, 할당이 실패하면 NULL을 반환
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    // 이전 메모리 블록의 크기를 헤더에서 읽어와 copySize에 저장
    copySize = GET_SIZE(HDRP(oldptr));

    // 복사해야 하는 데이터 크기를 새 크기와 이전 블록 크기 중 작은 값으로 설정
    if (size < copySize)
        copySize = size;

    // 이전 블록에서 새 블록으로 데이터를 복사
    memcpy(newptr, oldptr, copySize);

    // 이전 블록을 해제하고 새 블록 포인터를 반환
    mm_free(oldptr);
    return newptr;
}