#include "dryad_bsd_queue.h"

_(logic \bool mutable_qhead(QHead * x) = x != NULL ==> \mutable(x) && \writable(x))
_(logic \bool mutable_list(QNode * x) = x != NULL ==> \mutable(x) && \writable(x))

_(dryad)
QHead * simpleq_init()
  _(ensures queue(\result))
{

  QHead * head = (QHead *) malloc(sizeof(QHead));
  _(assume head != NULL)
  head->first = NULL;
  head->last = NULL; 
  return head;

}

