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

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) /* 8 */

#define WSIZE 4 /* 워드, 헤더/푸터 사이즈 (바이트) */
#define DSIZE 8 /* 더블워드 */
#define CHUNKSIZE (1<<12) /* 2^12 (4096 bytes = 4kb) 만큼 힙 확장 */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 블록크기 8의 배수, 2^3 -> 하위 3비트는 0 즉, 사이즈의 하위비트가 0이니 alloc 상태를 이 빈 하위비트에 저장 
* size = 24, alloc = 1 -> 0x18 | 0x1 = 0x19
*/
#define PACK(size, alloc) ((size) | (alloc))

/* 읽기/쓰기는 unsigned int */
#define GET(p) (*(unsigned int *)(p)) /* p가 참조하는 워드 리턴 */
#define PUT(p, val) (*(unsigned int *)(p) = (val)) /* p가 가리키는 워드에 val 저장 */

#define GET_SIZE(p) (GET(p) & ~0x7) /* & ~0111 -> 하위3비트 지움, 사이즈 비트만 남음 */
#define GET_ALLOC(p) (GET(p) & 0x1) /* 가장 오른쪽 비트 -> alloc flag(alloc=1, free=0) */ 

#define HDRP(bp) ((char *)(bp) - WSIZE) /* bp(페이로드 포인터) 의 1워드 앞은 헤더 */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /* 헤더에 있는 블록 사이즈에서 헤더+푸터(8바이트)를 빼면 페이로드 크기 -> 페이로드 포인터에서 그 크기만큼 더하면 푸터 */

/* 포인터 산술은 타입크기만큼 이동하기 때문에 char로 캐스팅해 1바이트로 조정 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) /* 헤더로 이동 후 사이즈를 get해 현재 페이로드 포인터에 더하면 다음 블록포인터 */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) /* 현재 포인터에서 2워드 뒤로 이동하면 이전 블록의 푸터 즉, 이전 블록의 사이즈를 알 수 있고 현재 블록에서 그 크기만큼 뒤로 가면 이전 블록포인터 */

/* footer elision 추가 매크로 */
#define PACKPA(size, alloc, prev_alloc) ((size) | (alloc) | (prev_alloc << 1))
#define GET_PREV_ALLOC(p) ((GET(p) >> 1) & 0x1) /* prev_alloc은 두번째 하위 비트 */
#define SET_PREV_ALLOC(hp)   (PUT((hp), GET(hp) | 0x2)) /* 다음 블록 헤더의 prev_alloc 비트 on/off */
#define CLEAR_PREV_ALLOC(hp) (PUT((hp), GET(hp) & ~0x2))

/* 시작 포인터 = 프롤로그 페이로드 */
static char *heap_listp = NULL;

#ifdef NEXT_FIT
static char *rover = NULL;
#endif

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) /* 16바이트 확보 */
        return -1;
    
    PUT(heap_listp, 0);                                  /* 정렬을 위한 4B 패딩 */
    PUT(heap_listp + (1*WSIZE), PACKPA(DSIZE, 1, 1));    /* 프롤로그 헤더 -> 힙의 양 끝 모서리 조건 제거를 위함 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));         /* 프롤로그 푸터 */
    PUT(heap_listp + (3*WSIZE), PACKPA(0, 1, 1));        /* 에필로드 헤더, 초기엔 프롤로그가 이전 블록이라 prev_alloc=1 */
    heap_listp += (2*WSIZE);                             /* 프롤로그 페이로드의 위치 */
    /* 블록 사이즈는 8의 배수 이므로 시작 bp가 8이면 payload 정렬이 끝까지 유지된다.
    * 8 + 8의 배수 = 다음 블록의 페이로드
    */

#ifdef NEXT_FIT
    rover = heap_listp;
#endif

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) /* 청크사이즈 바이트로 확장하고 초기 free block 생성 */
        return -1;

    return 0;
}

/* 1. 힙이 초기화 될 때
* 2. mm_malloc이 fit을 찾지 못했을 때 
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; /* 8의 배수 -> 정렬유지 */
    if ((long)(bp = mem_sbrk(size)) == -1) /* 사이즈 만큼의 추가 힙 공간 요청 */
        return NULL;
    
    int prev_alloc = GET_PREV_ALLOC(HDRP(bp)); /* 확장 전 에필로그의 prev_alloc = 직전 블록의 alloc */
    PUT(HDRP(bp), PACKPA(size, 0, prev_alloc)); /* 새 free block 헤더: prev_alloc 유지 */
    PUT(FTRP(bp), PACK(size, 0)); /* free만 footer 유지 */
    PUT(HDRP(NEXT_BLKP(bp)), PACKPA(0, 1, 0)); /* 새 에필로그: 바로 앞이 free → prev_alloc=0 */

    return coalesce(bp); /* 이전 힙이 free block으로 끝났다면 두 개의 free block 결합 */
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* adjusted size, 실제 할당 크기: 요청한 페이로드 + 헤더/푸터 오버헤드 + 정렬 */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;

    if (size == 0) /* 불필요한 요청 무시 */
        return NULL;

    asize = MAX(2*DSIZE, ALIGN(size + WSIZE)); /* 최소 블록 크기 16바이트vs요청사이즈+오버헤드4B를 8의 배수로 정렬한 것 -> 할당 블록은 푸터 없음 */

    if ((bp = find_fit(asize)) != NULL) /* 적절한 free block을 free list에서 찾았다면 */
    {
        place(bp, asize); /* 배치 -> 초과부분 분할(최소블록크기 이상) */
        return bp;
    }
    
    /* no fit found */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) /* 힙을 새로운 free block으로 확장 */
        return NULL;

    place(bp, asize); /* 요청한 block을 새 free block에 배치 */
    return bp; /* 새롭게 할당한 블록의 포인터 리턴 */
}

static void *find_fit(size_t asize)
{
    void *bp;
    
#ifdef FIRST_FIT
#warning "FIRST_FIT"
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) /* 힙 시작주소부터 - 에필로드 가드(헤더의 사이즈가 0 보다 클 때까지) - 다음 블록 페이로드 포인터로 이동 */
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) /* alloc이 0이고 사이즈가 할당해야 할 사이즈보다 크거나 같다면 */
            return bp;
    }
#elif defined(NEXT_FIT)
#warning "NEXT_FIT"
    for (bp = rover; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            rover = bp;
            return bp;
        }
    }
    for (bp = heap_listp; bp != rover; bp = NEXT_BLKP(bp)) /* 랩어라운드(wrap-around) -> 처음부터 */
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            rover = bp;
            return bp;
        }
    }
#elif defined(BEST_FIT)
#warning "BEST_FIT"
    void *best_bp = NULL;
    size_t best_sz = (size_t) - 1;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            if (GET_SIZE(HDRP(bp)) < best_sz)
            {
                best_sz = GET_SIZE(HDRP(bp));
                best_bp = bp;
            }
            
            if (asize == GET_SIZE(HDRP(bp))) /* 퍼펙트 핏 즉시 종료 */
                break;
        }
    }
    return best_bp;
#endif

    return NULL; /* no fit return null */
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    int prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) /* 최소 블록 크기 16bytes보다 크거나 같다면 분할 */
    {
        PUT(HDRP(bp), PACKPA(asize, 1, prev_alloc)); /* 새로 할당한 블록 배치 -> footer 없음 */
        
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACKPA(csize-asize, 0, 1)); /* 다음 블록 이동 후 초과부분 분할(free) -> 앞이 alloc이므로 prev_alloc=1 */
        PUT(FTRP(bp), PACK(csize-asize, 0));      /* free는 footer 생성 */

        /* free의 다음 블록 헤더 prev_alloc=0 */
        CLEAR_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
    }
    else /* 아니면 그냥 배치 -> 내부단편화 */
    {
        PUT(HDRP(bp), PACKPA(csize, 1, prev_alloc)); /* 통째로 할당 -> footer 없음 */
        SET_PREV_ALLOC(HDRP(NEXT_BLKP(bp))); /* 다음 블록 헤더 prev_alloc=1 */
    }
    
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    PUT(HDRP(bp), PACKPA(size, 0, prev_alloc)); /* 헤더에 alloc=0, prev_alloc 그대로 */
    PUT(FTRP(bp), PACK(size, 0));               /* free가 되었으니 footer 생성 */
    CLEAR_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));      /* 다음 블록은 이전이 free */

    coalesce(bp); /* 인접한 free block들과 결합 */
}

/* 프롤로그/에필로그로 인해 모서리 조건 작성x */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp)); /* 이전 블록의 alloc을 이전 푸터에서 읽음 -> 현재 헤더의 prev_alloc 비트로 교체 */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)                   /* case 1: 이전/다음 블록 모두 할당 */
        return bp;

    else if (prev_alloc && !next_alloc)             /* case 2: 이전 할당, 다음 가용 */
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); /* 다음 블록의 헤더에서 사이즈를 가져와서 더해줌 */
        /* 그 사이즈만큼의 free block 생성 */
        PUT(HDRP(bp), PACKPA(size, 0, GET_PREV_ALLOC(HDRP(bp)))); /* 현재 블록의 헤더 -> 그대로 */
        PUT(FTRP(bp), PACK(size, 0)); /* 헤더를 먼저 갱신해서 매크로식에 의해 자동으로 다음 블록의 푸터 자리 가리킴 */
    }

    /* PREV_BLKP는 prev_alloc이 0일 때만 사용(이전이 free → footer 존재). -> case 3,4 */
    else if (!prev_alloc && next_alloc)             /* case 3: 이전 가용, 다음 할당 */
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); /* 이전 블록의 헤더에서 사이즈를 가져와서 더해줌 -> prev가 free라 footer 존재 */
        PUT(FTRP(bp), PACK(size, 0)); /* 현재 블록의 푸터 -> 그대로 */
        PUT(HDRP(PREV_BLKP(bp)), PACKPA(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp))))); /* 이전 블록의 헤더 위치 */
        bp = PREV_BLKP(bp); /* 페이로드는 이전 블록으로 */
    }

    else                                            /* case 4: 이전/다음 모두 가용 */
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + /* 이전/다음 블록 사이즈를 합해서 더하고 */
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACKPA(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp))))); /* 이전 블록의 헤더 위치 */
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); /* 다음 블록의 푸터 위치 */
        bp = PREV_BLKP(bp); /* 페이로드는 이전 블록으로 */
    }
    
    CLEAR_PREV_ALLOC(HDRP(NEXT_BLKP(bp))); /* 결합 후 다음 헤더 prev_alloc=0 */

#ifdef NEXT_FIT
        /* 합쳐진 영역 안에 rover가 들어오면 합쳐진 새 블록의 바로 이전 블록에 rover를 둠.
        * 다음 탐색이 NEXT_BLKP(rover)에서 시작하므로, 첫 후보가 방금 합쳐진 큰 가용 블록이 됨.
        */
        if ((char *)bp <= rover && rover < (char *)bp + size)
        {
            rover = bp;
        }
#endif
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - WSIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;

    // if (oldptr == NULL) return mm_malloc(size);
    // if (size == 0) { mm_free(oldptr); return NULL; }

    // size_t old_blk = GET_SIZE(HDRP(oldptr));   // 헤더의 size 필드 (마스크 적용됨)
    // size_t old_pay = old_blk - WSIZE;          // footer elision: 할당 블록은 header 4B만 오버헤드

    // void *newptr = mm_malloc(size);
    // if (!newptr) return NULL;

    // size_t cpy = (size < old_pay) ? size : old_pay;   // 반드시 old_payload로 상한
    // memcpy(newptr, oldptr, cpy);
    // mm_free(oldptr);
    // return newptr;
}