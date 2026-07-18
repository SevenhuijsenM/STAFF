typedef struct {
  const int *data;
  int length;
} IntSeq;

typedef struct {
  const IntSeq *data;
  int length;
} IntSeqSeq;

/*@
  requires \valid_read(lists);
  requires lists->length >= 0;
  requires lists->length == 0 || \valid_read(lists->data + (0 .. lists->length - 1));
  requires \forall integer i; 0 <= i && i < lists->length ==> lists->data[i].length >= 0;
  requires \forall integer i; 0 <= i && i < lists->length ==> (lists->data[i].length == 0 || \valid_read(lists->data[i].data + (0 .. lists->data[i].length - 1)));
  assigns \nothing;
  ensures \result >= 0;
  ensures \result == lists->length;
*/
int CountLists(const IntSeqSeq *lists) {
  return lists->length;
}