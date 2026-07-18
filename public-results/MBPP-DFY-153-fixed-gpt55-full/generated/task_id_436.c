/*@ predicate IsNegativeValue(integer n) = n < 0; */

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> IsNegativeValue(n);
*/
int IsNegative(int n)
{
    return n < 0;
}

/*@
  requires len >= 0;
  requires len == 0 || \valid_read(arr + (0 .. len - 1));
  requires len == 0 || \valid(negativeList + (0 .. len - 1));
  requires len == 0 || \separated(arr + (0 .. len - 1), negativeList + (0 .. len - 1));

  assigns negativeList[0 .. len - 1];

  ensures 0 <= \result && \result <= len;

  ensures \forall integer k;
            0 <= k && k < \result ==>
              IsNegativeValue(negativeList[k]) &&
              (\exists integer j;
                 0 <= j && j < len && negativeList[k] == arr[j]);

  ensures \forall integer i;
            0 <= i && i < len && IsNegativeValue(arr[i]) ==>
              (\exists integer k;
                 0 <= k && k < \result && negativeList[k] == arr[i]);
*/
int FindNegativeNumbers(const int *arr, int len, int *negativeList)
{
    int count = 0;

    /*@
      loop invariant 0 <= i && i <= len;
      loop invariant 0 <= count && count <= i;

      loop invariant \forall integer k;
        0 <= k && k < count ==>
          IsNegativeValue(negativeList[k]);

      loop invariant \forall integer k;
        0 <= k && k < count ==>
          (\exists integer j;
             0 <= j && j < i && negativeList[k] == arr[j]);

      loop invariant \forall integer k;
        0 <= k && k < i && IsNegativeValue(arr[k]) ==>
          (\exists integer j;
             0 <= j && j < count && negativeList[j] == arr[k]);

      loop assigns i, count, negativeList[0 .. len - 1];
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        if (IsNegative(arr[i])) {
            //@ assert IsNegativeValue(arr[i]);
            negativeList[count] = arr[i];
            count++;
        }
    }

    return count;
}