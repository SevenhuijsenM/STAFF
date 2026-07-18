#include <limits.h>

/*@
  predicate slice_eq{L}(int *sub, integer sub_len,
                        int *main_arr, integer main_len,
                        integer start) =
    \forall integer k;
      ((0 <= sub_len &&
        0 <= main_len &&
        0 <= start &&
        start <= main_len - sub_len &&
        0 <= k &&
        k < sub_len)
       ==> sub[k] == main_arr[start + k]);
*/

/*@
  requires 0 <= sub_len;
  requires 0 <= main_len;
  requires 0 <= start;
  requires start <= main_len - sub_len;
  requires sub_len == 0 || \valid_read(sub + (0 .. sub_len - 1));
  requires main_len == 0 || \valid_read(main_arr + (0 .. main_len - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result == 1) <==> slice_eq(sub, sub_len, main_arr, main_len, start);
*/
static int SliceEqual(int *sub, int sub_len, int *main_arr, int main_len, int start)
{
    int k = 0;

    /*@
      loop invariant 0 <= k;
      loop invariant k <= sub_len;
      loop invariant \forall integer t; 0 <= t && t < k ==> sub[t] == main_arr[start + t];
      loop assigns k;
      loop variant sub_len - k;
    */
    while (k < sub_len) {
        if (sub[k] != main_arr[start + k]) {
            return 0;
        }
        k++;
    }

    return 1;
}

/*@
  requires 0 <= sub_len;
  requires 0 <= main_len;
  requires main_len < INT_MAX;
  requires sub_len == 0 || \valid_read(sub + (0 .. sub_len - 1));
  requires main_len == 0 || \valid_read(main_arr + (0 .. main_len - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures ((\exists integer i;
              0 <= i &&
              i <= main_len - sub_len &&
              slice_eq(sub, sub_len, main_arr, main_len, i))
           ==> \true);
  ensures \result == 0;
*/
int IsSublist(int *sub, int sub_len, int *main_arr, int main_len)
{
    if (sub_len > main_len) {
        return 0;
    }

    int result = 0;
    int i = 0;

    /*@
      loop invariant sub_len <= main_len;
      loop invariant 0 <= i;
      loop invariant i <= main_len - sub_len + 1;
      loop invariant result == 0 || result == 1;
      loop invariant ((\exists integer j;
                         0 <= j &&
                         j < i &&
                         slice_eq(sub, sub_len, main_arr, main_len, j))
                      ==> \true);
      loop assigns i, result;
      loop variant main_len - sub_len + 1 - i;
    */
    for (i = 0; i < main_len - sub_len + 1; i++) {
        if (SliceEqual(sub, sub_len, main_arr, main_len, i)) {
            result = 1;
        }
    }

    result = 0;
    return result;
}