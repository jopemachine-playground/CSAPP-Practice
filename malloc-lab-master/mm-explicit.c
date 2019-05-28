/*
 * mm-explicit.c - an empty malloc package
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 *
 * @id : 201502085 
 * @name : Lee Gyu Bong
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

#define ALIGNMENT 8
#define HDRSIZE 4
#define FTRSIZE 4
#define WSIZE 4
#define DSIZE 4
#define CHUNKSIZE (1<<12)
#define OVERHEAD 8

#define MAX(x,y) ((x) > (y) ? (x):(y))
#define MIN(x,y) ((x) < (y) ? (x):(y))

#define PACK(size,alloc) ((unsigned int)((size|alloc)))

#define GET(p) (*(unsigned int*)(p))
#define PUT(p,val) (*(unsigned int*)(p) = (unsigned int)(val))
#define GET8(p) (*(unsigned long*)(p))
#define PUT8(p) (*(unsigned long*)(p) = (unsigned long)(val))

#define HDRP(bp)       ((char *)(bp) - WSIZE)                    
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE))
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE((char*)(bp)))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define NEXT_FREEP(bp) ((char*)(bp))
#define PREV_FREEP(bp) ((char*)(bp) + WSIZE)

#define NEXT_FREE_BLKP(bp) ((char*)GET8((char*)(bp)))
#define PREV_FREE_BLKP(bp) ((char*)GET8((char*)(bp) + WSIZE))

#define ALIGN(p) (((size_t)(p) + (ALIGNMENT -1)) & ~0x7)

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

// 전역변수 

char* epilogue = 0;
char* h_ptr = 0;
// h_ptr은 힙의 첫 번째 블록을 가리키는 전역변수
char* heap_start = 0;
// heap_start는 init시 힙의 첫 번째를 가리키도록 함.

// 함수 선언

static void* extend_heap(size_t words);
static void place(void* bp, size_t asize);
static void* coalesce(void* bp);
static void checkheap(int verbose);
static void checkblock(void* bp);
static void* find_fit(size_t asize);

// 에러가 나면 -1, 정상일 경우 0 리턴.
int mm_init(void) {
	
	// mem_sbrk()로 힙 메모리를 요청하고 초기화. 에러가 발생하면 -1 리턴
	if((h_ptr = mem_sbrk(DSIZE +4 * HDRSIZE)) == NULL) return -1;

	// 힙의 시작위치를 가리키는 포인터 heap_start를 h_ptr로 초기화
	heap_start = h_ptr;

	PUT(h_ptr, NULL); // 0
	PUT(h_ptr + WSIZE, NULL); // 4
	PUT(h_ptr + DSIZE, 0); // 정렬 조건을 만족시키기 위한 패딩, 8
	PUT(h_ptr + DSIZE + HDRSIZE, PACK(OVERHEAD,1)); // 프롤로그 헤더, 12
	PUT(h_ptr + DSIZE + HDRSIZE + FTRSIZE, PACK(OVERHEAD,1)); // 프롤로그 풋터, 16 
	PUT(h_ptr + DSIZE + 2* HDRSIZE + FTRSIZE, PACK(0,1)); // 에필로그 헤더, 20

	/* 힙 포인터를 프롤로그의 header와 footer의 사이로 옮김 */
	h_ptr += DSIZE+DSIZE; 

	epilogue = h_ptr + HDRSIZE;

	// 가용블록을 할당. 오류가 발생하면 -1 리턴
	if(extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;

	return 0;
	
}

// 인라인 함수를 사용해 일반 함수로 작성했을 때 보다 높은 성능을 갖는 extend_heap을 작성

inline void* extend_heap(size_t words){

	unsigned int* old_epilogue;
	char* bp; 
	unsigned int size; // 힙 메모리에 대한 확장 요청 크기

	// 정렬 조건을 맞추기  위한 size 할당
	size = (words%2) ? (words+1)*WSIZE : words*WSIZE;

	// mem_sbrk()로 힙을 확장. 오류가 발생하면 NULL을 리턴하게 함.
	if((long)(bp = mem_sbrk(size)) < 0) return NULL;
	
	// old 에필로그 포인터를 저장한 후, 에필로그 교체
	old_epilogue = epilogue;
	epilogue = bp + size - HDRSIZE;

	// 헤더, 풋터, 새 에필로그 헤더를 만듬
	PUT(HDRP(bp), PACK(size,0));
	PUT(FTRP(bp), PACK(size,0));
	PUT(epilogue, PACK(0,1));

	// 힙 확장 후 가용 블록들을 연결
	return coalesce(bp);
}

static void* coalesce(void* bp){
    
  size_t size = GET_SIZE(HDRP(bp));
  
  // 앞이 할당되었는지, 뒤가 할당되었는지를 봐서 case를 4개로 쪼갠다. 
  switch(GET_ALLOC(FTRP(PREV_BLKP(bp))) | (GET_ALLOC(HDRP(NEXT_BLKP(bp))) << 1)){

	case 1:
	// 앞 블록만 할당되어 있던 경우 (뒤가 가용)
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp),PACK(size,0));
	PUT(FTRP(bp),PACK(size,0));
	break;

	case 2:
	// 뒷 블록만 할당되어 있던 경우 (앞은 가용)
	break;

	case 3: 
	// 둘 다 할당되어 있는 경우 (아무 작업도 하지 않고 bp를 반환)
	return bp;

	case 0:
	// 둘 다 가용블록인 경우
	break;

	}

  return bp;
}
        
void *malloc (size_t size) {
	
	char* bp; // payload의 첫 번째 바이트를 가리킴
	unsigned int asize; // 블록 사이즈는 alignment와 overhead에 조정됨
	unsigned int extendsize; // 맞는 가용 블록이 없을 때 extend할 사이즈

	// size가 올바르지 않을 때 예외 처리
	if (size == 0) return NULL;

	// block의 크기 결정
	if (size <= DSIZE) asize = 2*DSIZE;

	else
   	// size는 내가 할당하려는 블록의 크기, asize는 프롤로그, 헤더, 정렬을 위한 블록까지 포함한 (16바이트) 전체 블록의 크기
        // 주의 : implicit 버전. 수정이 필요할 수도 있음
	asize = DSIZE * (((size + DSIZE + (DSIZE -1))) / DSIZE);

	// 결정한 크기에 알맞은 블록을 list에서 검색하여 해당 위치에 할당
	if((bp = find_fit(asize)) !=NULL){
		place(bp, asize);
		return bp;
	}
	
	// free list에서 적절한 블록을 찾지 못했으면 힙을 늘려서 할당
	extendsize = MAX(asize, CHUNKSIZE);
	if((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;
	place(bp, asize);

	return bp;
}

static void* find_fit(size_t asize){
  /*
   언제나 프롤로그를 가리키는 heap_list_ptr에서 시작해, 전체 블록에서 가장
   먼저 할당 가능한 블록에 할당한다. (first fit 방식)

   implicit 에서의 first_fit과 다른 점은, 가용 블럭만을 검색한다는 것임.
   */ 
  void *bp;

  for (bp = h_ptr; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_FREE_BLKP(bp)) {
    if (asize <= GET_SIZE(HDRP(bp))) {
      return bp;
    }
  }
  return NULL; 
}

void free (void *ptr) {
        
	// 에러가 생긴 경우 리턴
	if(!ptr) return;

	// free 시킨 블록의 헤더와 풋터에 '할당' 마크를 없앰
	PUT(HDRP(ptr), PACK(GET_SIZE(HDRP(ptr)), 0));
	PUT(FTRP(ptr), PACK(GET_SIZE(HDRP(ptr)), 0));

	// free 후, 가용 블럭들을 연결
	coalesce(ptr);	

}

void *realloc(void *oldptr, size_t size) {
    return NULL;
}

void *calloc (size_t nmemb, size_t size) {
    return NULL;
}

static void place(void* bp, size_t asize){

    size_t csize = GET_SIZE(HDRP(bp));

    /*
       free블록이 24 바이트 (최소 가용 블럭의 크기)보다 큰 경우, 남은 가용블록에
       새로운 블록이 들어올 수 있기 때문에, 새로운 free블록을 만들어둔다.
    */
    if ((csize - asize) >= (3*DSIZE)) { 
       PUT(HDRP(bp), PACK(asize, 1));
       PUT(FTRP(bp), PACK(asize, 1));
       bp = NEXT_BLKP(bp);
       PUT(HDRP(bp), PACK(csize-asize, 0));
       PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    // 그렇지 않은 경우, 어차피 새로운 블록이 들어올 순 없기 때문에 그냥 둔다.
    else {
       PUT(HDRP(bp), PACK(csize, 1));
       PUT(FTRP(bp), PACK(csize, 1));
    }

}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.


static int in_heap(const void *p) {
    return p < mem_heap_hi() && p >= mem_heap_lo();
}


 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */

/*
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}
*/


/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
	checkheap(verbose);
}

void checkheap(int verbose)
{
}

static void checkblock(void *bp)
{
}
