typedef struct {
  int *data;
  int length;
} IntSeq;

typedef struct {
  int **data;
  int *lengths;
  int length;
} IntSeqSeq;

/*@
  requires 0 <= lst.length;
  requires lst.length == 0 || \valid_read(lst.data + (0 .. lst.length - 1));
  requires lst.length == 0 || \valid_read(lst.lengths + (0 .. lst.length - 1));
  requires lst.length == 0 || \valid(result_buffer + (0 .. lst.length - 1));
  requires \forall integer i; 0 <= i && i < lst.length ==> lst.lengths[i] > 0;
  requires \forall integer i; 0 <= i && i < lst.length ==> \valid_read(lst.data[i] + (0 .. lst.lengths[i] - 1));
  requires lst.length == 0 || \separated(result_buffer + (0 .. lst.length - 1), lst.data + (0 .. lst.length - 1));
  requires lst.length == 0 || \separated(result_buffer + (0 .. lst.length - 1), lst.lengths + (0 .. lst.length - 1));
  requires \forall integer i; 0 <= i && i < lst.length ==> \separated(result_buffer + (0 .. lst.length - 1), lst.data[i] + (0 .. lst.lengths[i] - 1));
  assigns result_buffer[0 .. lst.length - 1];
  ensures \result.length == lst.length;
  ensures \result.data == result_buffer;
  ensures \forall integer i; 0 <= i && i < \result.length ==> \result.data[i] == lst.data[i][0];
*/
IntSeq GetFirstElements(IntSeqSeq lst, int *result_buffer)
{
  IntSeq result;
  result.data = result_buffer;
  result.length = lst.length;

  int i = 0;

  /*@
    loop invariant 0 <= i && i <= lst.length;
    loop invariant result.length == lst.length;
    loop invariant result.data == result_buffer;
    loop invariant \forall integer j; 0 <= j && j < i ==> result_buffer[j] == lst.data[j][0];
    loop assigns i, result_buffer[0 .. lst.length - 1];
    loop variant lst.length - i;
  */
  while (i < lst.length) {
    result_buffer[i] = lst.data[i][0];
    i++;
  }

  return result;
}