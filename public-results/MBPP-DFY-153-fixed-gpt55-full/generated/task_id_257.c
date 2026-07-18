typedef struct {
  int length;
  int data[2];
} IntSeq2;

/*@
  assigns \nothing;
  ensures \result.length == 2;
  ensures \result.data[0] == b;
  ensures \result.data[1] == a;
*/
IntSeq2 Swap(int a, int b) {
  IntSeq2 result;
  result.length = 2;
  result.data[0] = b;
  result.data[1] = a;
  return result;
}