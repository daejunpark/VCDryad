#include "dryad_dll_mem_reg_defs.h"

_(logic \bool mutable_list(MemReg * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
MemReg * memory_region_init(BackingFile * file_, 
                            int file_offset_, 
                            int file_size_, 
                            int start_address_, 
                            int size_)
  _(ensures \result != NULL)
  _(ensures \result->file          == file_
         && \result->file_offset   == file_offset_
         && \result->file_size     == file_size_
         && \result->start_address == start_address_
         && \result->size          == size_
         && \result->prev          == NULL
         && \result->next          == NULL )
  _(ensures dll(\result))
{
  MemReg * mr = (MemReg *) malloc(sizeof(MemReg));
  _(assume mr != NULL)
  mr->file = file_;
  mr->file_offset = file_offset_;
  mr->file_size = file_size_;
  mr->start_address = start_address_;
  mr->size = size_;
  mr->prev = NULL;
  mr->next = NULL;
  return mr;
}

_(dryad)
MemReg * memory_region_create_user_space_region()
  _(ensures dll(\result))
{
  MemReg * r  = memory_region_init(NULL, 0, 0, 0, 1);
  _(assume mutable_list(r))
  MemReg * r1 = memory_region_init(NULL, 0, 0, 786432, 65536);
  _(assume mutable_list(r1))
  r->next = r1;
  r1->prev = r;
  return r;
}

_(dryad)
MemReg * split_memory_region(MemReg * curr, int offset)
  _(requires curr != NULL)
  _(requires dll(curr))
  _(requires offset > 0 && offset % 4096 == 0)
  _(requires curr->start_address + offset < INT_MAX)
  _(ensures dll(curr))
  _(ensures dll(\result))
{
  _(assume mutable_list(curr))
  if (offset >= curr->size) {
    return NULL;
  }

  MemReg * old_next = curr->next;
  MemReg * next = NULL;
  if (offset > curr->file_size) {
    next = (MemReg *) malloc(sizeof(MemReg));
    _(assume next != NULL)
    next->file = NULL;
    next->file_offset = 0;
    next->file_size = 0;
    int curr_s = curr->start_address;
    int curr_so = curr_s + offset;
    next->start_address = curr_so;
    int tmp_size = curr->size - offset;
    next->size = tmp_size;
    next->prev = NULL;
    next->next = NULL;
  } else {
    next = (MemReg *) malloc(sizeof(MemReg));
    _(assume next != NULL)
    BackingFile * bf = curr->file;
    next->file = bf;
    next->file_offset = 0;
    next->file_size = 0;
    int curr_s = curr->start_address;
    int curr_so = curr_s + offset;
    next->start_address = curr_so;
    int tmp_size = curr->size - offset;
    next->size = tmp_size;
    next->prev = NULL;
    next->next = NULL;
    curr->file_size = offset;
  }

  curr->size = offset;
  next->prev = curr;
  next->next = old_next;

  if(old_next != NULL) {
    _(assume mutable_list(old_next))
    old_next->prev = next;
  }
  curr->next = next;
  return next;
}


