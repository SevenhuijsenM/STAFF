#include <stdbool.h>

/*@
  requires a_len >= 0;
  requires b_len >= 0;
  requires a_len == 0 || \valid_read(a + (0 .. a_len - 1));
  requires b_len == 0 || \valid_read(b + (0 .. b_len - 1));
  assigns \nothing;
  ensures \result ==> \exists integer i, j; 0 <= i && i < a_len && 0 <= j && j < b_len && a[i] == b[j];
  ensures !\result ==> \forall integer i, j; 0 <= i && i < a_len && 0 <= j && j < b_len ==> a[i] != b[j];
*/
bool HasCommonElement(const int *a, int a_len, const int *b, int b_len)
{
    bool result = false;
    int i;

    /*@
      loop invariant 0 <= i && i <= a_len;
      loop invariant result == false;
      loop invariant \forall integer k, j; 0 <= k && k < i && 0 <= j && j < b_len ==> a[k] != b[j];
      loop assigns i, result;
      loop variant a_len - i;
    */
    for (i = 0; i < a_len; i++) {
        int j;

        /*@
          loop invariant 0 <= i && i < a_len;
          loop invariant 0 <= j && j <= b_len;
          loop invariant result == false;
          loop invariant \forall integer k, l; 0 <= k && k < i && 0 <= l && l < b_len ==> a[k] != b[l];
          loop invariant \forall integer k; 0 <= k && k < j ==> a[i] != b[k];
          loop assigns j, result;
          loop variant b_len - j;
        */
        for (j = 0; j < b_len; j++) {
            if (a[i] == b[j]) {
                result = true;
                return result;
            }
        }
    }

    return result;
}