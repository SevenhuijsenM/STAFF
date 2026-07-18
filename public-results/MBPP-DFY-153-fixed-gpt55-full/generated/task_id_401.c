#include <limits.h>

/*@
  requires rows > 0;
  requires \valid_read(row_offsets + (0 .. rows));
  requires row_offsets[0] == 0;
  requires \forall integer i, j; 0 <= i && i <= j && j <= rows ==> row_offsets[i] <= row_offsets[j];
  requires 0 <= row_offsets[rows];

  requires row_offsets[rows] == 0 || \valid_read(a + (0 .. row_offsets[rows] - 1));
  requires row_offsets[rows] == 0 || \valid_read(b + (0 .. row_offsets[rows] - 1));
  requires row_offsets[rows] == 0 || \valid(result + (0 .. row_offsets[rows] - 1));

  requires row_offsets[rows] == 0 || \separated(result + (0 .. row_offsets[rows] - 1), a + (0 .. row_offsets[rows] - 1));
  requires row_offsets[rows] == 0 || \separated(result + (0 .. row_offsets[rows] - 1), b + (0 .. row_offsets[rows] - 1));
  requires row_offsets[rows] == 0 || \separated(result + (0 .. row_offsets[rows] - 1), row_offsets + (0 .. rows));

  requires \forall integer p; 0 <= p && p < row_offsets[rows] ==> INT_MIN <= (integer)a[p] + (integer)b[p];
  requires \forall integer p; 0 <= p && p < row_offsets[rows] ==> (integer)a[p] + (integer)b[p] <= INT_MAX;

  assigns result[0 .. row_offsets[rows] - 1];

  ensures \forall integer p; 0 <= p && p < row_offsets[rows] ==> result[p] == (integer)a[p] + (integer)b[p];

  ensures \forall integer i; 0 <= i && i < rows ==> 0 <= row_offsets[i];
  ensures \forall integer i; 0 <= i && i < rows ==> row_offsets[i] <= row_offsets[i + 1];

  ensures \forall integer i, j;
    0 <= i && i < rows &&
    0 <= j && j < row_offsets[i + 1] - row_offsets[i]
    ==> result[row_offsets[i] + j] == (integer)a[row_offsets[i] + j] + (integer)b[row_offsets[i] + j];
*/
void IndexWiseAddition(const int *a, const int *b, int *result, const int *row_offsets, int rows)
{
  int total = row_offsets[rows];

  //@ assert 0 <= total;

  /*@
    loop invariant 0 <= p;
    loop invariant p <= total;
    loop invariant total == row_offsets[rows];
    loop invariant \forall integer q; 0 <= q && q < p ==> result[q] == (integer)a[q] + (integer)b[q];
    loop assigns p, result[0 .. total - 1];
    loop variant total - p;
  */
  for (int p = 0; p < total; p++) {
    //@ assert 0 <= p;
    //@ assert p < row_offsets[rows];
    //@ assert INT_MIN <= (integer)a[p] + (integer)b[p];
    //@ assert (integer)a[p] + (integer)b[p] <= INT_MAX;
    result[p] = a[p] + b[p];
    //@ assert result[p] == (integer)a[p] + (integer)b[p];
  }
}