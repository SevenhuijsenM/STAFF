#include <stddef.h>

/*@
  requires 0 <= arr_len;
  requires 0 <= L && L <= arr_len;

  requires arr_len == 0 || \valid_read(arr + (0 .. arr_len - 1));
  requires L == 0 || \valid(firstPart + (0 .. L - 1));
  requires arr_len - L == 0 || \valid(secondPart + (0 .. arr_len - L - 1));
  requires \valid(firstPart_len);
  requires \valid(secondPart_len);

  requires \separated(firstPart_len, secondPart_len);

  requires arr_len > 0 ==> \separated(firstPart_len, arr + (0 .. arr_len - 1));
  requires arr_len > 0 ==> \separated(secondPart_len, arr + (0 .. arr_len - 1));

  requires L > 0 ==> \separated(firstPart_len, firstPart + (0 .. L - 1));
  requires L > 0 ==> \separated(secondPart_len, firstPart + (0 .. L - 1));

  requires arr_len - L > 0 ==> \separated(firstPart_len, secondPart + (0 .. arr_len - L - 1));
  requires arr_len - L > 0 ==> \separated(secondPart_len, secondPart + (0 .. arr_len - L - 1));

  requires (L > 0 && arr_len - L > 0) ==> \separated(firstPart + (0 .. L - 1), secondPart + (0 .. arr_len - L - 1));
  requires (arr_len > 0 && L > 0) ==> \separated(arr + (0 .. arr_len - 1), firstPart + (0 .. L - 1));
  requires (arr_len > 0 && arr_len - L > 0) ==> \separated(arr + (0 .. arr_len - 1), secondPart + (0 .. arr_len - L - 1));

  assigns firstPart[0 .. L - 1], secondPart[0 .. arr_len - L - 1], *firstPart_len, *secondPart_len;

  ensures *firstPart_len == L;
  ensures *secondPart_len == arr_len - L;

  ensures \forall integer i; 0 <= i && i < L ==> firstPart[i] == \old(arr[i]);
  ensures \forall integer i; 0 <= i && i < arr_len - L ==> secondPart[i] == \old(arr[L + i]);

  ensures \forall integer i; 0 <= i && i < arr_len ==>
            (i < L ? firstPart[i] == \old(arr[i]) : secondPart[i - L] == \old(arr[i]));
*/
void SplitArray(const int *arr,
                int arr_len,
                int L,
                int *firstPart,
                int *firstPart_len,
                int *secondPart,
                int *secondPart_len)
{
    *firstPart_len = L;
    *secondPart_len = arr_len - L;

    int i = 0;

    /*@
      loop invariant 0 <= i && i <= L;
      loop invariant *firstPart_len == L;
      loop invariant *secondPart_len == arr_len - L;
      loop invariant \forall integer k; 0 <= k && k < i ==> firstPart[k] == \at(arr[k], Pre);
      loop assigns i, firstPart[0 .. L - 1];
      loop variant L - i;
    */
    while (i < L) {
        firstPart[i] = arr[i];
        i++;
    }

    int j = 0;

    /*@
      loop invariant 0 <= j && j <= arr_len - L;
      loop invariant *firstPart_len == L;
      loop invariant *secondPart_len == arr_len - L;
      loop invariant \forall integer k; 0 <= k && k < L ==> firstPart[k] == \at(arr[k], Pre);
      loop invariant \forall integer k; 0 <= k && k < j ==> secondPart[k] == \at(arr[L + k], Pre);
      loop assigns j, secondPart[0 .. arr_len - L - 1];
      loop variant arr_len - L - j;
    */
    while (j < arr_len - L) {
        secondPart[j] = arr[L + j];
        j++;
    }
}