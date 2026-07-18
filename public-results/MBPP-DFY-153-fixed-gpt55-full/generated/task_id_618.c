#include <limits.h>

/*@
  requires a_len >= 0;
  requires b_len >= 0;
  requires a_len == b_len;
  requires a_len == 0 || \valid_read(a + (0 .. a_len - 1));
  requires b_len == 0 || \valid_read(b + (0 .. b_len - 1));
  requires a_len == 0 || \valid(result + (0 .. a_len - 1));
  requires \forall integer i; 0 <= i && i < b_len ==> b[i] != 0;
  requires \forall integer i; 0 <= i && i < a_len ==> !(a[i] == INT_MIN && b[i] == -1);
  requires a_len == 0 || \separated(result + (0 .. a_len - 1), a + (0 .. a_len - 1));
  requires a_len == 0 || \separated(result + (0 .. a_len - 1), b + (0 .. b_len - 1));
  assigns result[0 .. a_len - 1];
  ensures \result == a_len;
  ensures \forall integer i; 0 <= i && i < \result ==> result[i] == a[i] / b[i];
*/
int ElementWiseDivide(const int *a, int a_len, const int *b, int b_len, int *result) {
    int result_len = 0;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= a_len;
      loop invariant a_len == b_len;
      loop invariant result_len == i;
      loop invariant \forall integer k; 0 <= k && k < i ==> result[k] == a[k] / b[k];
      loop assigns i, result_len, result[0 .. a_len - 1];
      loop variant a_len - i;
    */
    while (i < a_len) {
        result[result_len] = a[i] / b[i];
        result_len++;
        i++;
    }

    return result_len;
}