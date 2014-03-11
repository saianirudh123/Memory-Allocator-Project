/* 
 * This is Dynamic memory Allocator (DMA) based on explicit free
 * lists, first fit placement, and boundary tag coalescing. 
 * Blocks must be aligned to doubleword (8 byte) 
 * boundaries. Minimum block size is 16 bytes. 
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

team_t team = {
	
	"Hawks",
	
	"AR SAI ANIRUDH ",
	
	" 201201197@daiict.ac.in",
	
	"Pericherla Avinash",
	
	" 201201236@daiict.ac.in"
};

#define WSIZE      sizeof(void *) //Size of a word 
#define DSIZE      (2 * WSIZE)    // Size of a double word (2 * size of word)
#define CHUNKSIZE  (1 << 12)      // The heap will be increased by this size 


#define MAX(x, y)  ((x) > (y) ? (x) : (y))  // Computes the maximum of 2 variables


#define PACK(size, alloc)  ((size) | (alloc)) // This macro embedds the size and allocation status into a word.


#define GET(p)       (*(uintptr_t *)(p)) // This macro reads a word at location p 
#define PUT(p, val)  (*(uintptr_t *)(p) = (val)) // This macro puts or writes a word at location p


#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))  // This macro returns the size at a location p 
#define GET_ALLOC(p)  (GET(p) & 0x1) //This macro returns the allocated status at a location p

#define HDRP(bp)  ((char *)(bp) - WSIZE) // Returns the address of the Header of that particular block
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // Returns the address of the Footer of that particular block


#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // This Payload returns the payload address of the Next block
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // This Payload returns the payload address of the prev block



#define NEXT_FREE(bp) *(int *)(bp)
#define PreviousFreeBlock(ptr) (*(void **) (ptr))// This returns the previous free block in the explicictly maitained free list
#define NextFreeBlock(ptr) (*(void **) (ptr + WSIZE))// This returns the next free block in the explicitly maitained free list
#define SetPreviousFree(bp, previous) (*((void **)(bp)) = previous)
#define SetNextFree(bp, next) (*((void **)(bp + WSIZE)) = next)


static void *coalesce(void *bp); //Coalesces a newly created free block with its adjacent blocks after checking the necessary conditions
static void *extend_heap(size_t words);// This routine extends the heap to a predefined size known as chunk size.
static void *find_fit(size_t total_size);// This is the key routine which finds the necessary free block of appropriate size for allocation 
static void place(void *bp, size_t total_size);

//Heap checker routines
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 


static char *head;  //This is the pointer used to maintain the explicit free list


static char *heap_listp;   // this is the block pointer to the heap. it remains constant
static char *htp;//This is the pointer pointing to the heap

// Newly added Routines
void Add_Free_Block(void *bp,size_t size_of_block); // Adds a newly created free block to the explictly maintained free list
void Delete_Free_Block(void *bp,size_t size_of_block); // Deletes a newly allocated block from the explicitly maintained free list


/*
* mm_init - It is the routine responsible for the initialization of 
* malloc package. This routine is similar to the implicit free list init function
* In this particular definition we are defining a head pointer and initializing it to 
* null
*/

int mm_init(void)
{
htp=mem_sbrk(55*DSIZE); // 55 lists being created
if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
return -1;
PUT(heap_listp, 0);                 // Alignment padding 
PUT(heap_listp+WSIZE, PACK(DSIZE, 1)); //Prologue header 
PUT(heap_listp+DSIZE, PACK(DSIZE, 1)); // Prologue footer 
PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1)); // Epilogue header 
heap_listp += DSIZE;
int i=0;
head=htp;
while(i<55){
	SetNextFree(htp+i*DSIZE,0);  // Initialize head to NULL ( yet no free block )
	++i;
}

if (extend_heap(CHUNKSIZE/WSIZE) == (void *)-1)/* Extend the empty heap with a free block of CHUNKSIZE bytes */
return -1;
return 0;

}

/*
* extend_heap : Extends heap to CHUNKSIZE while initialising the heap.
*/

static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;
	// Allocate an even number of words to maintain alignment. 
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);
	// Initialize free block header/footer and the epilogue header. 
	PUT(HDRP(bp), PACK(size, 0));         // Packs the size and the allocations status(0) into a word and put into header
	PUT(FTRP(bp), PACK(size, 0));         // Packs the size and the allocations status(0) into a word and put into footer
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  //
	//Coalesces if the previous block is free
	return (coalesce(bp));
}

/* Add_Free_Block : This routine add's a free block to the explicitly maintained
 * free list . It makes work easier in the way that , if we want a free block to
 * be allocated, we can just traverse the free list. It follows the lifo property
 * simalar to stack
 */ 
void Add_Free_Block(void *bp,size_t size_of_block) {
	//following Stack property
    void *ptr = bp;

	int num=size_of_block/6000;//Hash index calculation
	if(num>=50)
	   num=49;
	char *p=htp;

	head=p+DSIZE*num; //Direct's the function to that particular list

	if(NextFreeBlock(head)==0){
		SetNextFree(head,ptr);// Pointer rearrangement 

		SetPreviousFree(ptr,head);// Pointer rearrangements
		SetNextFree(ptr,0);

}
	else{
		SetPreviousFree(NextFreeBlock(head),ptr);// Freeing the previous pointer of the next block to the present block and assiging it to ptr
		SetNextFree(ptr,NextFreeBlock(head));//setting the next pointer of ptr to the previously next block
		SetNextFree(head,ptr);// Pointer rearrangements
		SetPreviousFree(ptr,head);// Pointer rearrangements

}

}
// Delete_Free_BLock : This routine helps in updating the list 
 // when a free block is alllocated , or any block which is already free
 // is extended while coalescing. The link of the free list is removed 
 // from the explicitly maintained list.
 //
void Delete_Free_Block(void *bp, size_t size_of_block) {
	int num	= size_of_block/6000; // Hash Index
	if(num >= 50)
		num = 49;
	char *p = htp;
	head = p+DSIZE*num;
	void *next_blk = (void *) NextFreeBlock(bp); // Gives the next free block pointer
	void *previous_blk = (void *) PreviousFreeBlock(bp);// Gives the previous free block pointer
	if(*(void **)(head + WSIZE)==0)
		return;
	
	else{
		if (previous_blk == head && next_blk!=0) {
		SetNextFree(head,next_blk); // Sets the next block in the list to free
		SetPreviousFree(next_blk,head);// Sets the previous block in the list to free
		
      } 
	else if(previous_blk!=head && next_blk!=0){
		SetNextFree(previous_blk, next_blk);// Sets the next block in the list to free
		SetPreviousFree(next_blk,previous_blk);// Sets the previous block in the list to free
		
	}

	else if (previous_blk==head && next_blk == 0) {
		SetNextFree(previous_blk,0);// Sets the next block in the list to free
		
	}
	else if (previous_blk!=head && next_blk == 0) {
		SetNextFree(previous_blk,0);// Sets the next block in the list to free
		
	}
}
}

//coalesce : This routine coalesces the adjacent free blocks to reduce fragmentation
// error . In this routine we are also updating the explicitly maintained free list 
// with the new coalesced free blocks and deleting the old fragments.

void *coalesce(void *ptr) {
	bool PreviousAllocated = GET_ALLOC(FTRP(PREV_BLKP(ptr)));// Get allocated status of the previous block
	bool NextAllocated = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));// Get the allocated status of the next block
	size_t size = GET_SIZE(HDRP(ptr));// Size of the present block
	
	// Since Previous and Next are free it coalesces the three of them and return the pointer to
	//the previous block
	if(!PreviousAllocated && !NextAllocated) {
		Delete_Free_Block(PREV_BLKP(ptr),GET_SIZE(HDRP(PREV_BLKP(ptr))));// Deletes the Prev free block from the explicitly maintained list
		Delete_Free_Block(NEXT_BLKP(ptr),GET_SIZE(HDRP(NEXT_BLKP(ptr))));// Deletes the Next free block from the explicitly maintained list
		size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + 
		    GET_SIZE(HDRP(NEXT_BLKP(ptr)));//calulation of the total new size to be allocated at the new pointer location
		PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));// packs the size of the block and the allocation(0) status in the header
		PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));// packs the size of the block and the allocation(0) status in the footer
		ptr = PREV_BLKP(ptr);
		Add_Free_Block(ptr,size);// Adds free block to the explicitly maintained free list
	}
	 //Since the previous and next blocks are allocated 
	// It doesnt do any thing and adds a link between the nely created free block
	else if (PreviousAllocated && NextAllocated) {
		Add_Free_Block(ptr,size);// Adds free block to the explicitly maintained free list
		return ptr;
	}
		// Since the previous block is free and next block is allocated the previous
	//block is coalesced with the present block and the pointer to the previous block
	else if (!PreviousAllocated && NextAllocated) {
		Delete_Free_Block(PREV_BLKP(ptr),GET_SIZE(HDRP(PREV_BLKP(ptr))));
		size += GET_SIZE(HDRP(PREV_BLKP(ptr)));//calulation of the total new size to be allocated at the new pointer location
		PUT(FTRP(ptr), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
		ptr = PREV_BLKP(ptr);
		Add_Free_Block(ptr,size);// Adds free block to the explicitly maintained free list
	}
//Since the next block is free the next block is coalesced with the previous block 
	//and the pointer to the present block is retuernd
	else if (PreviousAllocated && !NextAllocated) {
		Delete_Free_Block(NEXT_BLKP(ptr),GET_SIZE(HDRP(NEXT_BLKP(ptr))));// Deletes the previously embedded block from the explicictly maintained free list
		size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));//calulation of the total new size to be allocated at the new pointer location
		PUT(HDRP(ptr), PACK(size, 0));// packs the size of the block and the allocation(0) status in the header
		PUT(FTRP(ptr), PACK(size, 0));// packs the size of the block and the allocation(0) status in the footer
		Add_Free_Block(ptr,size);// Adds free block to the explicitly maintained free list
}


return ptr; // return the void pointer anyway we are not getting to catch it 
}

// mm_malloc : This routine is allocating a new block by incrementing the 
// the brk pointer. It takes care of the the alignment requirements


void *mm_malloc(size_t size)
{
	size_t total_size, extendsize; // adjusted block size 
	void *bp; // amount to extend heap if no fit 

	if (size == 0)//since size is null does no allocation
		return (NULL);

	// Adjusts the block size to include overhead and alignment requirments.
	if (size <= DSIZE)
		total_size = 2 * DSIZE;
	else
		total_size = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	if ((bp = find_fit(total_size)) != NULL) //finds the fit required to be placed from the exlicictly maintained list
	{

		place(bp, total_size);//places th block in the list
		return bp;
}

	extendsize = MAX(total_size,CHUNKSIZE);// calculates the max of the total required size and the previously provided chunk size
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)//extends the size of the heap if the size requirments is not met
		return NULL;


	place(bp, total_size); // places the block into the heap

	return bp;
}


/* find_fit : This is the key routine in the DMA implimentation. It moves
 * throughout the explicitly maintained free list, and checks for the suitable 
 * free block required for allocation, returns the pointer to that block or returns
 * null
 */

void *find_fit(size_t total_size) {
	void *bp;


	char *p=htp;
	int num=total_size/6000; // Hash Index
	if(num>=50)
		num=49;
	char *k;
	for(num;num<50;num++){
		k=p+DSIZE*num; // directs to the particular list where the ree block has to be inserted

	for (bp = NextFreeBlock(k); (bp != 0)&&(k<p+DSIZE*50); bp = NextFreeBlock(bp)) //  This is traversing the whole explicictly maintained free list to get the exact
		// or nearly exact fit for allocation
	{
		if (total_size <= GET_SIZE(HDRP(bp)))// checks the size with the required size.
		   return bp;
    }
  }
return NULL; // no fit 
}



void place(void *bp, size_t total_size) {
	size_t csize = GET_SIZE(HDRP(bp));//computes the size of the block


	if ((csize - total_size) >= (2*DSIZE )) {
		Delete_Free_Block(bp,csize);//Deletes the bly maintaock from the explicictly maintained free list
		PUT(HDRP(bp), PACK(total_size, 1));//packs the size of the block and the allocation(1) status in the footer
		PUT(FTRP(bp), PACK(total_size, 1));//packs the size of the block and the allocation(1) status in the header
		bp = NEXT_BLKP(bp);//gets the next block pointer
		PUT(HDRP(bp), PACK(csize-total_size, 0));//packs the size of the block and the allocation(0) status in the footer
		PUT(FTRP(bp), PACK(csize-total_size, 0));//packs the size of the block and the allocation(0) status in the header

		Add_Free_Block(bp,csize-total_size);//Adds the newly created block to the explicitly maintained free list
	}

/* do not split */
	else {
		PUT(HDRP(bp), PACK(csize, 1));//packs the size of the block and the allocation(1) status in the header
		PUT(FTRP(bp), PACK(csize, 1));//packs the size of the block and the allocation(1) status in the footer
		Delete_Free_Block(bp,csize);//Deletes the block  from the explicictly maintained free list
	}

}


/*
* mm_free - Freeing a block does nothing.
* Point to note is that we call coalesce as soon as we free the block
* This is what we call Immediate Coalescing ( this avoids fragmentation ).
*/

void mm_free(void *ptr)
{

	size_t size = GET_SIZE(HDRP(ptr));//Calculates the size of the newly creates free block
	PUT(HDRP(ptr), PACK(size, 0));// Packs the size of the block and the allocation status of the block in the header
	PUT(FTRP(ptr), PACK(size, 0));// Packs the size of the block and the allocation status of the block in the footer
	coalesce(ptr); // coalesces the newly block in the explicictly maintained list


}

/*
* mm_realloc : This routine is a kind of a wrapper routine for the already implimented
* mm_malloc and mm_free routines. It also takes care of the reallocation of a new 
* pointer or memory space.
*/
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize= GET_SIZE(HDRP(ptr)),total_size;// Gets the present size of the allocated block which has to be reallocated
	void *newptr;

    // If size == 0 It means it's a free block. We return NULL 
	if (size == 0) {
		mm_free(ptr);// frees the block 
		return (NULL);
	}

	/* If ptr is NULL, It means we have freshly allocate ablock with the mentioned size*/
	if (ptr == NULL)
		return (mm_malloc(size));// allaoctes the block of the mentioned size.
	if (size <= DSIZE)
		total_size = 2 * DSIZE;
			else
		total_size = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);// calcuates the total_size required for the new block to be allocated
	if(oldsize == total_size) return ptr;
	if (oldsize >= total_size) 
	{
		
		if((oldsize - total_size) != (DSIZE))
		{
			if((oldsize - total_size) != 0)
			{
				PUT(HDRP(ptr), PACK(total_size, 1));//packs the size of the block and the allocation(1) status in the header
				PUT(FTRP(ptr), PACK(total_size, 1));//packs the size of the block and the allocation(1) status in the footer
				void *bp = NEXT_BLKP(ptr);//Gets the pointer of the next block in the heap
				PUT(HDRP(bp), PACK(oldsize - total_size, 0));//packs the size of the block and the allocation(0) status in the header
				PUT(FTRP(bp), PACK(oldsize - total_size, 0));//packs the size of the block and the allocation(1) status in the footer
				coalesce(bp);// coaleseces the block 
			}
			return ptr;
		}
		
		
	}	
	size_t next_blkp_size = (size_t)GET_SIZE(HDRP(NEXT_BLKP(ptr)));
	if((size_t)GET_ALLOC(HDRP(NEXT_BLKP(ptr)))==0   &&   next_blkp_size + oldsize - total_size > DSIZE)
	{
		Delete_Free_Block(NEXT_BLKP(ptr),next_blkp_size);//Deletes the block  from the explicictly maintained free list
		PUT(HDRP(ptr), PACK(total_size, 1));//packs the size of the block and the allocation(1) status in the header
		PUT(FTRP(ptr), PACK(total_size, 1));//packs the size of the block and the allocation(1) status in the footer
		void *bp = NEXT_BLKP(ptr);
		PUT(HDRP(bp), PACK(next_blkp_size + oldsize - total_size, 0));//packs the size of the block and the allocation(0) status in the header
		PUT(FTRP(bp), PACK(next_blkp_size + oldsize - total_size, 0));//packs the size of the block and the allocation(0) status in the footer
		Add_Free_Block(bp,next_blkp_size + oldsize - total_size);//Adds the block to the explicictly maintained free list
		//checkheap(1);
		return ptr;
	}
	
	
	newptr = mm_malloc(size);// allocates the new block at the new pointer

	//If realloc() fails the original block is left untouched  
	if (newptr == NULL)
		return (NULL);
	

	// Copy the old data. 
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	// Free the old block. 
	mm_free(ptr);

	return (newptr);
}

static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp))){
		size_t h=GET(HDRP(bp));
		size_t f=GET(FTRP(bp));
		size_t preh=GET(HDRP(PREV_BLKP(bp)));
		printf("Error: header %zu does not match footer %zu %p and previous block %zu\n,",h,f,bp,preh);
		
}
}


void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}


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


