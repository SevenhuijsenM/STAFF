#include <stdbool.h>

/*@
  requires 0 <= sequences_len;
  requires sequences_len == 0 || \valid_read(sequence_lengths + (0 .. sequences_len - 1));
  requires \forall integer i; 0 <= i && i < sequences_len ==> 0 <= sequence_lengths[i];
  assigns \nothing;
  ensures (\result == true) <==> 
          (\forall integer i, j;
             0 <= i && i < sequences_len &&
             0 <= j && j < sequences_len
             ==> sequence_lengths[i] == sequence_lengths[j]);
*/
bool AllSequencesEqualLength(const int *sequence_lengths, int sequences_len)
{
    if (sequences_len == 0) {
        return true;
    }

    int firstLength = sequence_lengths[0];
    bool result = true;
    int i;

    /*@
      loop invariant 1 <= i && i <= sequences_len;
      loop invariant firstLength == sequence_lengths[0];
      loop invariant (result == true) <==>
        (\forall integer k;
           0 <= k && k < i ==> sequence_lengths[k] == firstLength);
      loop assigns i, result;
      loop variant sequences_len - i;
    */
    for (i = 1; i < sequences_len; i++) {
        if (sequence_lengths[i] != firstLength) {
            result = false;
        }
    }

    return result;
}