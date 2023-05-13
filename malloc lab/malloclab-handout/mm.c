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
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 头部/脚部的大小 */
#define WSIZE 4
/* 双字 */
#define DSIZE 8

/* 扩展堆时的默认大小 */
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
/* 设置头部和脚部的值, 块大小+分配位 */
#define PACK(size, alloc) ((size) | (alloc))

/* 读写指针p的位置 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) ((*(unsigned int *)(p)) = (val))

/* 从头部或脚部获取大小或分配位 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 给定有效载荷指针, 找到头部和脚部 */
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 给定有效载荷指针, 找到前一块或下一块 */
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

/* 给定序号，找到链表头节点位置 */
#define GET_HEAD(num) ((unsigned int *)(long)(GET(heap_list + WSIZE * num)))
/* 给定bp,找到前驱和后继 */
#define GET_PRE(bp) ((unsigned int *)(long)(GET(bp)))
#define GET_SUC(bp) ((unsigned int *)(long)(GET((unsigned int *)bp + 1)))

/* 设置类的数量 */
#define CLASS_SIZE 20

static char* heap_list;

static void* extend_heap(size_t words);
static void place(void* ptr, size_t asize);
static void* coalesce(void *bp);
static void* find_fit(size_t size); 
static int search(size_t size);
static void insert(void *bp);
static void delete(void *bp);


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 申请空间 */
    if((heap_list = mem_sbrk((4+CLASS_SIZE)*WSIZE)) == (void *)-1) return -1;
    /* 初始化20个大小的类头指针 */
    for (int i = 0; i < CLASS_SIZE; i++) {
        PUT(heap_list + i * WSIZE, 0);
    }
    PUT(heap_list + CLASS_SIZE * WSIZE, 0);                              /* 对齐 */

    /*
     * 序言块和结尾块均设置为已分配，方便考虑边界情况
    */
    PUT(heap_list + ((1 + CLASS_SIZE) * WSIZE), PACK(DSIZE, 1));        /* 填充序言块头部 */
    PUT(heap_list + ((2 + CLASS_SIZE) * WSIZE), PACK(DSIZE, 1));        /* 填充序言块尾部 */
    PUT(heap_list + ((3 + CLASS_SIZE) * WSIZE), PACK(0, 1));            /* 结尾块 */

    /* 扩展空闲空间 */
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extend_size;
    char *bp;
    if (size == 0) return NULL;
    if (size <= DSIZE) asize = 2 * DSIZE; // 至少16字节
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 向上与8字节对齐

    // 寻找合适的空闲块
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    // 找不到则扩展堆
    extend_size = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL) return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (ptr == 0) return;
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if (!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if (size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/*
*   扩展heap，传入的是字节数
*/
void *extend_heap(size_t words){
    /* bp总是指向有效载荷 */
    char *bp;
    size_t size;
    /* 根据传入字节数的奇偶性，考虑对齐 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    /* 分配 */
    if((long)(bp = mem_sbrk(size)) == -1) return NULL;

    /* 设置头部和尾部 */
    PUT(HDRP(bp), PACK(size, 0));            /* 空闲块头 */
    PUT(FTRP(bp), PACK(size, 0));            /* 空闲块脚 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));    /* 新结尾块设置*/

    /* 判断相邻块是否是空闲块，进行合并 */
    return coalesce(bp);
}

/* place 分离空闲块 */
static void place(void* ptr, size_t asize) {
    size_t block_size = GET_SIZE(HDRP(ptr));
    /* 将要分配ptr，因此将ptr指向的块从空闲链表中删除*/
    delete(ptr);

    if ((block_size - asize) >= (2 * DSIZE)) { // 需要截断
        PUT(HDRP(ptr), PACK(asize, 1));        // 修改头部
        PUT(FTRP(ptr), PACK(asize, 1));        // 沿着刚修改的头部，找到重新定位后的尾部
        ptr = NEXT_BLKP(ptr);                  // 沿着刚修改的头部，找到未分配块的有效载荷
        PUT(HDRP(ptr), PACK(block_size - asize, 0));   // 修改空闲块头部的分配大小
        PUT(FTRP(ptr), PACK(block_size - asize, 0));   // 修改空闲块尾部的分配大小
        /* 将分离出来的空闲块加入空闲链表中 */
        insert(ptr);
    } else { // 不需要截断，修改头部尾部即可
        PUT(HDRP(ptr), PACK(block_size, 1));
        PUT(FTRP(ptr), PACK(block_size, 1));
    }
}

/*
*   合并空闲块
*/
void *coalesce(void * bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));        /* 前一块是否分配 */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));        /* 后一块是否分配 */
    size_t size = GET_SIZE(HDRP(bp));                          /* 当前块大小 */

    if (prev_alloc && next_alloc) { // Case 1
        insert(bp);
        return bp;                                            /*前后都已分配，直接将空闲块插入链表 */
    }

    else if (prev_alloc && !next_alloc) { // Case 2
        // 后一块空闲，前一块不空闲
        delete(NEXT_BLKP(bp));                               /* 将后面的块从其链表中删除 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));               /* 更新新的空闲块大小 */
        PUT(HDRP(bp), PACK(size, 0));                        /* 修改空闲块头部 */
        PUT(FTRP(bp), PACK(size, 0));                        /* 修改空闲块尾部 */
    }

    else if (!prev_alloc && next_alloc) { // Case 3
        // 前一块空闲，后一块不空闲
        delete(PREV_BLKP(bp));                               /* 将其前面的块从链表中删除 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));               /* 更新新的空闲块大小 */
        PUT(FTRP(bp), PACK(size, 0));                        /* 修改空闲块尾部 */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));             /* 找到前块空闲块的头部进行修改 */
        bp = PREV_BLKP(bp);
    }

    else { // Case 4
        // 前后块均空闲
        /* 将前后两个块都从其链表中删除 */
        delete(PREV_BLKP(bp));
        delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));  /* 更新新的空闲块大小 */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));             /* 找到前块空闲块的头部进行修改 */
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));             /* 找到后块空闲块的尾部进行修改 */
        bp = PREV_BLKP(bp);
    }

    /* 空闲表准备好后，将其插入合适位置 */
    insert(bp);
    return bp;
}

void *find_fit(size_t size) {
    int num = search(size);
    unsigned int* bp;
    /* 如果找不到合适的块，则搜索下一个更大的空闲链表 */
    while (num < CLASS_SIZE) {
        bp = GET_HEAD(num);
        /* 如果bp在当前空闲链表不为空，则继续寻找*/
        while (bp) {
            if (GET_SIZE(HDRP(bp)) >= size) return (void *)bp;
            bp = GET_SUC(bp);
        }
        /* 否则在下一个空闲链表中进行寻找 */
        num++;
    }
    return NULL;
}

/* search - 找到块大小对应的等价类的序号*/
int search(size_t size) {
    int i = 0;
    for (i = 4; i <= 22; i++) {
        if (size <= (1 << i)) return i - 4;
    }
    return i - 4;
}

/* insert，插入块，将块插到链表头部*/
void insert(void *bp){
    /* 获取块的大小 */
    size_t size = GET_SIZE(HDRP(bp));
    /* 获取空闲链表的头序号*/
    int num = search(size);
    if (GET_HEAD(num) == NULL) {            // 若为空，则直接放入
        PUT(heap_list + WSIZE * num, bp);
        PUT(bp, NULL);                     //  前驱
        PUT((unsigned int *)bp + 1, NULL); //  后继 
    } else {                               // 不为空，则将块插入链表头
        /* 双向链表连接 */
        PUT((unsigned int *)bp + 1, GET_HEAD(num));     // bp的后继放原来的第一个节点
        PUT(GET_HEAD(num), bp);                         // 原来第一个节点的前驱放bp
        PUT(bp, NULL);                                  // bp的前驱为空
        PUT(heap_list + WSIZE * num, bp);               // 头结点放bp
    }
}

/* delete 删除块，将双向链表中的某一个节点删除*/
void delete(void *bp){
    /* 获取块的大小 */
    size_t size = GET_SIZE(HDRP(bp));
    /* 获取空闲链表的头序号*/
    int num = search(size);
    /* 分四种情况 */

    /* 1.当bp为唯一节点，后继为null，前驱为null
    *  直接将头结点设置为null
    */
    if (GET_PRE(bp) == NULL && GET_SUC(bp) == NULL) {
        PUT(heap_list + num * WSIZE, NULL);
    }

    /* 2.当bp是最后一个节点
    *  将bp前驱节点的后继设置为null即可
    */
    else if (GET_PRE(bp) != NULL && GET_SUC(bp) == NULL) {
        PUT(GET_PRE(bp) + 1, NULL);
    }

    /* 3.当bp是第一个节点时
    *  将头结点设置为bp的后继节点即可
    */
    else if (GET_PRE(bp) == NULL && GET_SUC(bp) != NULL) {
        PUT(heap_list + num * WSIZE, GET_SUC(bp));
        PUT(GET_SUC(bp), NULL);
    }

    /* 4.当bp是中间节点时
    *  需要将bp的前驱节点和后继节点连接
    */
    else {
        PUT(GET_PRE(bp) + 1, GET_SUC(bp));
        PUT(GET_SUC(bp), GET_PRE(bp));
    } 
}

