#include <stdbool.h>

/*@
  requires len >= 0;
  requires len == 0 || \valid_read(a + (0 .. len - 1));
  assigns \nothing;
  ensures \result == true <==> (\exists integer j; 0 <= j && j < len && a[j] == value);
*/
bool ContainsValue(const int *a, int len, int value)
{
    int j = 0;

    /*@
      loop invariant 0 <= j && j <= len;
      loop invariant \forall integer k; 0 <= k && k < j ==> a[k] != value;
      loop assigns j;
      loop variant len - j;
    */
    while (j < len) {
        if (a[j] == value) {
            return true;
        }
        j++;
    }

    return false;
}

/*@
  requires len1 >= 0;
  requires len2 >= 0;
  requires len1 == 0 || \valid_read(seq1 + (0 .. len1 - 1));
  requires len2 == 0 || \valid_read(seq2 + (0 .. len2 - 1));
  assigns \nothing;
  ensures \result == true <==>
          (\exists integer i;
             0 <= i && i < len1 &&
             (\exists integer j;
                0 <= j && j < len2 && seq2[j] == seq1[i]));
*/
bool AnyValueExists(const int *seq1, int len1, const int *seq2, int len2)
{
    bool result = false;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= len1;
      loop invariant result == true <==>
        (\exists integer k;
           0 <= k && k < i &&
           (\exists integer j;
              0 <= j && j < len2 && seq2[j] == seq1[k]));
      loop assigns i, result;
      loop variant len1 - i;
    */
    while (i < len1 && result == false) {
        if (ContainsValue(seq2, len2, seq1[i])) {
            result = true;
        }
        i++;
    }

    return result;
}