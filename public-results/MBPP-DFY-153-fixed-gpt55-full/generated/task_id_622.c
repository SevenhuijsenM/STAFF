#include <limits.h>

/*@
  requires a_len == b_len;
  requires a_len > 0;
  requires b_len > 0;
  requires \valid_read(a + (0 .. a_len - 1));
  requires \valid_read(b + (0 .. b_len - 1));
  requires \forall integer i; 0 <= i && i < a_len - 1 ==> a[i] <= a[i + 1];
  requires \forall integer i; 0 <= i && i < b_len - 1 ==> b[i] <= b[i + 1];
  requires a_len % 2 != 0 ||
           (a_len >= 2 &&
            INT_MIN <= (integer)a[a_len / 2 - 1] + (integer)b[0] &&
            (integer)a[a_len / 2 - 1] + (integer)b[0] <= INT_MAX);

  assigns \nothing;

  behavior even_length:
    assumes a_len % 2 == 0;
    ensures \result == (a[a_len / 2 - 1] + b[0]) / 2;

  behavior odd_length:
    assumes a_len % 2 != 0;
    ensures \result == a[a_len / 2];

  complete behaviors;
  disjoint behaviors;
*/
int FindMedian(const int *a, int a_len, const int *b, int b_len)
{
    (void)b_len;

    if (a_len % 2 == 0) {
        return (a[a_len / 2 - 1] + b[0]) / 2;
    } else {
        return a[a_len / 2];
    }
}