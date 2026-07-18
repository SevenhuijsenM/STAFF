#include <limits.h>

/*@ predicate IsOddLogic(integer n) = n % 2 != 0; */

/*@ predicate InArray{L}(integer x, int *a, integer n) =
      \exists integer j; 0 <= j && j < n && a[j] == x;
*/

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> IsOddLogic(n);
*/
int IsOdd(int n)
{
    return n % 2 != 0;
}

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(arr + (0 .. n - 1));
  requires n == 0 || \valid(oddList + (0 .. n - 1));
  requires n == 0 || \separated(arr + (0 .. n - 1), oddList + (0 .. n - 1));

  assigns oddList[0 .. n - 1];

  ensures 0 <= \result && \result <= n;

  ensures \forall integer k;
            0 <= k && k < \result ==>
              IsOddLogic(oddList[k]) && InArray(oddList[k], arr, n);

  ensures \forall integer k;
            0 <= k && k < n && IsOddLogic(arr[k]) ==>
              InArray(arr[k], oddList, \result);
*/
int FilterOddNumbers(int *arr, int n, int *oddList)
{
    int count = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant 0 <= count && count <= i;

      loop invariant \forall integer k;
        0 <= k && k < count ==>
          IsOddLogic(oddList[k]) && InArray(oddList[k], arr, n);

      loop invariant \forall integer k;
        0 <= k && k < i && IsOddLogic(arr[k]) ==>
          InArray(arr[k], oddList, count);

      loop assigns i, count, oddList[0 .. n - 1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (IsOdd(arr[i])) {
            oddList[count] = arr[i];
            count++;
        }
    }

    return count;
}