#include <limits.h>

typedef struct {
  int *data;
  int length;
} IntArray;

/*@
  requires a.length == b.length;
  requires 0 <= a.length;
  requires a.length == 0 || \valid_read(a.data + (0 .. a.length-1));
  requires b.length == 0 || \valid_read(b.data + (0 .. b.length-1));
  requires a.length == 0 || \valid(result_data + (0 .. a.length-1));
  requires a.length == 0 || \separated(result_data + (0 .. a.length-1), a.data + (0 .. a.length-1));
  requires a.length == 0 || \separated(result_data + (0 .. a.length-1), b.data + (0 .. b.length-1));
  requires \forall integer i; 0 <= i && i < a.length ==> INT_MIN <= (integer)a.data[i] - (integer)b.data[i];
  requires \forall integer i; 0 <= i && i < a.length ==> (integer)a.data[i] - (integer)b.data[i] <= INT_MAX;

  assigns \result, result_data[0 .. a.length-1]
    \from a.length, result_data, a.data[0 .. a.length-1], b.data[0 .. b.length-1];

  ensures \result.length == a.length;
  ensures \result.data == result_data;
  ensures \forall integer i; 0 <= i && i < \result.length ==> \result.data[i] == (integer)a.data[i] - (integer)b.data[i];
*/
IntArray ElementWiseSubtraction(IntArray a, IntArray b, int *result_data)
{
  IntArray result;
  result.data = result_data;
  result.length = a.length;

  int i = 0;

  /*@
    loop invariant 0 <= i && i <= a.length;
    loop invariant result.length == a.length;
    loop invariant result.data == result_data;
    loop invariant a.length == 0 || \valid(result_data + (0 .. a.length-1));
    loop invariant \forall integer k; 0 <= k && k < i ==> result_data[k] == (integer)a.data[k] - (integer)b.data[k];
    loop assigns i, result_data[0 .. a.length-1];
    loop variant a.length - i;
  */
  while (i < a.length) {
    result_data[i] = a.data[i] - b.data[i];
    i = i + 1;
  }

  return result;
}