/*@ predicate IsOddValue(integer n) =
      \exists integer q; n == 2 * q + 1;
*/

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> IsOddValue(n);
*/
int IsOdd(int n)
{
    int r = n % 2;
    return r != 0;
}

/*@
  requires 0 <= n;
  requires n == 0 || \valid_read(arr + (0 .. n-1));
  requires n == 0 || \valid(oddList + (0 .. n-1));
  requires n == 0 || \separated(arr + (0 .. n-1), oddList + (0 .. n-1));
  assigns oddList[0 .. n-1];
  ensures 0 <= \result && \result <= n;
  ensures \forall integer k;
            0 <= k && k < \result ==>
              IsOddValue(oddList[k]);
  ensures \forall integer k;
            0 <= k && k < \result ==>
              \exists integer j;
                0 <= j && j < n && arr[j] == oddList[k];
  ensures \forall integer j;
            0 <= j && j < n && IsOddValue(arr[j]) ==>
              \exists integer k;
                0 <= k && k < \result && oddList[k] == arr[j];
*/
int FindOddNumbers(const int *arr, int n, int *oddList)
{
    int count = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant 0 <= count && count <= i;
      loop invariant \forall integer k;
                        0 <= k && k < count ==>
                          IsOddValue(oddList[k]);
      loop invariant \forall integer k;
                        0 <= k && k < count ==>
                          \exists integer j;
                            0 <= j && j < i && arr[j] == oddList[k];
      loop invariant \forall integer j;
                        0 <= j && j < i && IsOddValue(arr[j]) ==>
                          \exists integer k;
                            0 <= k && k < count && oddList[k] == arr[j];
      loop assigns i, count, oddList[0 .. n-1];
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