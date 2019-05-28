/*
 * mm-implicit.c - an empty malloc package
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

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define WSIZE 4
#define DSIZE 8
#define CHUNK_SIZE (1<<12)
#define OVERHEAD 8
#define MAX(x,y) ((x) > (y)? (x):(y))
#define PACK(size,alloc) ((size)|(alloc))
#define GET(p) (*(unsigned int*)(p))
#define PUT(p,val) (*(unsigned int*)(p) = (val))
#define GET_SIZE(p) ((GET(p) & ~0x7))
#define HDRP(bp)       ((char *)(bp) - WSIZE)                    
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define GET_ALLOCED(p) (GET(p) & 0x1)
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE))
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE))

// 보고서에 괄호가 필요한 이유를 작성

// heap_list_ptr은 언제나 프롤로그를 가리키는 전역변수
static char* heap_list_ptr = 0;
// next_fit에 사용될 전역변수
static char* next_fit_ptr = 0;

static void* extend_heap(size_t words);
static void place(void* bp, size_t asize);

/*
 더 나은 점수를 위해 next_fit 알고리즘을 선택
 */
//#define find_fit first_fit 
#define find_fit next_fit 
//#define find_fit best_fit 

static void* first_fit(size_t asize);
static void* next_fit(size_t asize);
static void* best_fit(size_t asize);

static void* coalesce(void* bp);

static void printblock(void* bp);
static void checkheap(int verbose);
static void checkblock(void* bp);

int mm_init(void) {
	
	mem_init();

	if((heap_list_ptr = mem_sbrk(4*WSIZE)) == (void*)-1)
		return -1;
 	
	PUT(heap_list_ptr, 0); // 처음 (그냥 의미 없는 값. 뭐가 들어가도 상관 없음)
	PUT(heap_list_ptr + (1*WSIZE), PACK(DSIZE,1)); // 프롤로그
	PUT(heap_list_ptr + (2*WSIZE), PACK(DSIZE,1)); // 프롤로그
	PUT(heap_list_ptr + (3*WSIZE), PACK(0,1)); // 에필로그 헤더
	heap_list_ptr += DSIZE;
	
	// 초기화 되면 next_fit_ptr이 프롤로그를 가리키게 함.
	next_fit_ptr = heap_list_ptr;
	
	// 1024만큼 extend. 
	// 실제로 쓸 땐 4를 곱해서 사용.

	if(extend_heap(CHUNK_SIZE/WSIZE) == NULL)
		return -1;
		
	return 0;
}

static void *extend_heap(size_t words){

    char *bp;
    size_t size;

    // 4096 (4를 다시 곱해줌)
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;                                        

    PUT(HDRP(bp), PACK(size, 0));  // 헤더에도 풋터에도 size를 저장.        
    PUT(FTRP(bp), PACK(size, 0));        
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 

    return coalesce(bp);   

}

static void* coalesce(void* bp){
    
  size_t size = GET_SIZE(HDRP(bp));
  
  // 앞이 할당되었는지, 뒤가 할당되었는지를 봐서 case를 4개로 쪼갠다. 
  
  switch(GET_ALLOCED(FTRP(PREV_BLKP(bp))) | (GET_ALLOCED(HDRP(NEXT_BLKP(bp))) << 1)){

	case 1:
	// 앞 블록만 할당되어 있던 경우 (뒤가 가용)
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    	PUT(HDRP(bp), PACK(size, 0));
    	PUT(FTRP(bp), PACK(size, 0));
	break;

	case 2:
	// 뒷 블록만 할당되어 있던 경우 (앞은 가용)
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
	break;

	case 3: 
	// 둘 다 할당되어 있는 경우 (아무 작업도 하지 않고 bp를 반환)
	return bp;

	case 0:
	// 둘 다 가용블록인 경우
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
	break;

  }

  /*
     coalesce 작업 후, 가용블록이 변했다면 (case 3이 아닌 경우)
     next_fit_ptr을 bp로 변경시켜야 한다.

  */ 

  next_fit_ptr = bp;

  return bp;
}



static void* first_fit(size_t asize){
  /*
   언제나 프롤로그를 가리키는 heap_list_ptr에서 시작해, 전체 블록에서 가장
   먼저 할당 가능한 블록에 할당한다.
   */ 
  void *bp;

  for (bp = heap_list_ptr; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOCED(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
      return bp;
    }
  }
  return NULL; 
}

static void* next_fit(size_t asize){
 
  char *bp = next_fit_ptr;
  
  // 우선 다음 블록부터 검색해본다.
  
  while(GET_SIZE(HDRP(next_fit_ptr)) > 0){
	  if(!GET_ALLOCED(HDRP(next_fit_ptr)) && (asize <= GET_SIZE(HDRP(next_fit_ptr)))) return next_fit_ptr;	
	  next_fit_ptr = NEXT_BLKP(next_fit_ptr);
  }
  
  // 다음 블록부터 검색해봤는데 없다. -> 앞쪽에 가용이 있을 수 있으니 바로 NULL을 리턴하고 extend_heap 하면 안 됨
  // 처음 블록부터 다시 bp까지 검색한다. 항상 프롤로그를 가리키는 heap_list_ptr을 이용.
  
  for(next_fit_ptr = heap_list_ptr; next_fit_ptr < bp; next_fit_ptr = NEXT_BLKP(next_fit_ptr))
	 if(!GET_ALLOCED(HDRP(next_fit_ptr)) && (asize <= GET_SIZE(HDRP(next_fit_ptr))))
    		  return next_fit_ptr;
  
  return NULL;
}

static void* best_fit(size_t asize){
/*
 가장 사이즈가 잘 맞는 블록을 찾아 bp를 리턴할 것.
*/ 
    char* index_ptr = heap_list_ptr;
    char* minbp = NULL;
    int isFirst = 1;

	while (GET_SIZE(HDRP(index_ptr)) > 0) {
	    // 가용블록의 크기가 asize보다 크거나 같고, 할당이 안 되 있고 minbp가 가리키는 공간의 크기보다 작다면 minbp를 교체
	    if (!GET_ALLOCED(HDRP(index_ptr)) && (asize <= GET_SIZE(HDRP(index_ptr)))){
	    	
	    	if (isFirst) {
			// 처음 찾은 index_ptr을 minbp에 저장
			minbp = index_ptr;
			isFirst = 0;
		}
		
		else {
			// 두 번째 부턴, 찾은 블록과 지금까지의 가장 작은 블록의 크기를 비교
			if(GET_SIZE(HDRP(index_ptr)) < GET_SIZE(HDRP(minbp))) minbp = index_ptr;
		}
		
	    }
	    // 다음 블록으로
	    index_ptr = NEXT_BLKP(index_ptr);
  	}
    // 찾은 블록이 없다면 Null을 return
    return minbp;
}

static void place(void* bp, size_t asize){

    size_t csize = GET_SIZE(HDRP(bp));
    
    /* 
       free블록이 16 바이트보다 큰 경우, 남은 가용블록에 
       새로운 블록이 들어올 수 있기 때문에, 새로운 free블록을 만들어둔다.
    */
    if ((csize - asize) >= (2*DSIZE)) {
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

void* malloc(size_t size) {
    size_t asize;    
    size_t extendsize;
    char *bp;

  if (heap_list_ptr == 0){
    mm_init();
  }
  if (size == 0)
    return NULL;

  if (size <= DSIZE)                                         
    asize = 2*DSIZE;                                        
  else
    // size는 내가 할당하려는 블록의 크기, asize는 프롤로그, 헤더, 정렬을 위한 블록까지 포함한 (16바이트) 전체 블록의 크기
    asize = DSIZE * (((size + DSIZE + (DSIZE -1))) / DSIZE);

  if ((bp = find_fit(asize)) != NULL) {  
    place(bp, asize);                  
    return bp;
  }

  extendsize = MAX(asize,CHUNK_SIZE);                
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
    return NULL;                                 
  
  place(bp, asize);                             
  return bp;
	
}

void mm_free(void *bp)
{

  if (bp == 0)
    return;

  size_t size = GET_SIZE(HDRP(bp));

  if (heap_list_ptr == 0){
    mm_init();
  }

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);
}

void *realloc(void *oldptr, size_t size) {
  size_t oldsize;
  void *newptr;

  if(size == 0) {
    mm_free(oldptr);
    return 0;
  }

  if(oldptr == NULL) {
    return mm_malloc(size);
  }

  newptr = mm_malloc(size);

  if(!newptr) {
    return 0;
  }

  oldsize = GET_SIZE(HDRP(oldptr));
  if(size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  mm_free(oldptr);

  return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
*/

void mm_checkheap(int verbose){
  checkheap(verbose);
}

void *calloc (size_t nmemb, size_t size) {
  
  // mm-naive.c와 동일   
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;

}

static void printblock(void *bp)
{
  size_t hsize, halloc, fsize, falloc;

  checkheap(0);
  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOCED(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOCED(FTRP(bp));

  if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

  printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp,
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
 * checkheap - Minimal check of the heap for consistency
 */
void checkheap(int verbose)
{
  char *bp = heap_list_ptr;

  if (verbose)
    printf("Heap (%p):\n", heap_list_ptr);

  if ((GET_SIZE(HDRP(heap_list_ptr)) != DSIZE) || !GET_ALLOCED(HDRP(heap_list_ptr)))
    printf("Bad prologue header\n");
  checkblock(heap_list_ptr);

  for (bp = heap_list_ptr; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose)
      printblock(bp);
    checkblock(bp);
  }

  if (verbose)
    printblock(bp);
  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOCED(HDRP(bp))))
    printf("Bad epilogue header\n");
}

