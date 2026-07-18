#include <limits.h>

/*@
  requires first_len > 0;
  requires second_len >= 0;
  requires first_len - 1 <= INT_MAX - second_len;
  requires first != \null;
  requires second != \null;
  requires result != \null;
  requires \valid_read(first + (0 .. first_len - 1));
  requires \valid_read(second + (0 .. second_len - 1));
  requires \valid(result + (0 .. first_len - 2 + second_len));
  requires \separated(result + (0 .. first_len - 2 + second_len), first + (0 .. first_len - 1));
  requires \separated(result + (0 .. first_len - 2 + second_len), second + (0 .. second_len - 1));
  assigns result[0 .. first_len - 2 + second_len];
  ensures \result == first_len - 1 + second_len;
  ensures \forall integer i; 0 <= i && i < first_len - 1 ==> result[i] == \old(first[i]);
  ensures \forall integer i; first_len - 1 <= i && i < \result ==> result[i] == \old(second[i - first_len + 1]);
*/
int ReplaceLastElement(const int *first, int first_len,
                       const int *second, int second_len,
                       int *result)
{
    int i = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= first_len - 1;
      loop invariant \forall integer k; 0 <= k && k < i ==> result[k] == first[k];
      loop assigns i, result[0 .. first_len - 2];
      loop variant first_len - 1 - i;
    */
    while (i < first_len - 1) {
        result[i] = first[i];
        i++;
    }

    int j = 0;

    /*@
      loop invariant 0 <= j;
      loop invariant j <= second_len;
      loop invariant i == first_len - 1;
      loop invariant \forall integer k; 0 <= k && k < first_len - 1 ==> result[k] == first[k];
      loop invariant \forall integer k; 0 <= k && k < j ==> result[first_len - 1 + k] == second[k];
      loop assigns j, result[first_len - 1 .. first_len - 2 + second_len];
      loop variant second_len - j;
    */
    while (j < second_len) {
        result[first_len - 1 + j] = second[j];
        j++;
    }

    return first_len - 1 + second_len;
}