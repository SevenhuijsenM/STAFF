/*@
  predicate IsEven(integer n) =
    n % 2 == 0;

  predicate InArray{L}(int const *a, integer n, integer v) =
    \exists integer i;
      0 <= i && i < n &&
      \valid_read{L}(a + i) &&
      \at(a[i], L) == v;
*/

/*@
  requires 0 <= arr_len;
  requires arr_len == 0 || \valid_read(arr + (0 .. arr_len - 1));
  requires arr_len == 0 || \valid(evenList + (0 .. arr_len - 1));
  requires arr_len == 0 ||
    \separated(arr + (0 .. arr_len - 1), evenList + (0 .. arr_len - 1));

  assigns evenList[0 .. arr_len - 1];

  ensures 0 <= \result;
  ensures \result <= arr_len;

  ensures \forall integer k;
    0 <= k && k < arr_len ==> arr[k] == \old(arr[k]);

  ensures \forall integer k;
    0 <= k && k < \result ==>
      IsEven(evenList[k]) && InArray{Pre}(arr, arr_len, evenList[k]);

  ensures \forall integer k;
    0 <= k && k < arr_len && IsEven(\old(arr[k])) ==>
      InArray{Here}(evenList, \result, \old(arr[k]));
*/
int RemoveOddNumbers(int const *arr, int arr_len, int *evenList)
{
    int even_count = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= arr_len;
      loop invariant 0 <= even_count;
      loop invariant even_count <= i;

      loop invariant \forall integer k;
        0 <= k && k < arr_len ==> arr[k] == \at(arr[k], Pre);

      loop invariant \forall integer k;
        0 <= k && k < even_count ==>
          IsEven(evenList[k]) && InArray{Pre}(arr, arr_len, evenList[k]);

      loop invariant \forall integer k;
        0 <= k && k < i && IsEven(arr[k]) ==>
          InArray{Here}(evenList, even_count, arr[k]);

      loop assigns i, even_count, evenList[0 .. arr_len - 1];
      loop variant arr_len - i;
    */
    for (int i = 0; i < arr_len; i++) {
        //@ assert 0 <= i;
        //@ assert i < arr_len;
        //@ assert arr[i] == \at(arr[i], Pre);

        if (arr[i] % 2 == 0) {
            //@ assert IsEven(arr[i]);
            //@ assert InArray{Pre}(arr, arr_len, arr[i]);
            //@ assert 0 <= even_count;
            //@ assert even_count <= i;
            //@ assert even_count < arr_len;

            evenList[even_count] = arr[i];

            //@ assert evenList[even_count] == arr[i];
            //@ assert IsEven(evenList[even_count]);
            //@ assert InArray{Pre}(arr, arr_len, evenList[even_count]);
            //@ assert \valid_read(evenList + even_count);
            //@ assert InArray{Here}(evenList, even_count + 1, arr[i]);

            /*@ assert \forall integer k;
                  0 <= k && k < even_count ==>
                    IsEven(evenList[k]) && InArray{Pre}(arr, arr_len, evenList[k]);
            */

            /*@ assert \forall integer k;
                  0 <= k && k < even_count + 1 ==>
                    IsEven(evenList[k]) && InArray{Pre}(arr, arr_len, evenList[k]);
            */

            /*@ assert \forall integer k;
                  0 <= k && k < i && IsEven(arr[k]) ==>
                    InArray{Here}(evenList, even_count, arr[k]);
            */

            /*@ assert \forall integer k;
                  0 <= k && k < i && IsEven(arr[k]) ==>
                    InArray{Here}(evenList, even_count + 1, arr[k]);
            */

            even_count++;

            //@ assert 0 <= even_count;
            //@ assert even_count <= i + 1;

            /*@ assert \forall integer k;
                  0 <= k && k < even_count ==>
                    IsEven(evenList[k]) && InArray{Pre}(arr, arr_len, evenList[k]);
            */

            /*@ assert \forall integer k;
                  0 <= k && k < i + 1 && IsEven(arr[k]) ==>
                    InArray{Here}(evenList, even_count, arr[k]);
            */
        } else {
            //@ assert !IsEven(arr[i]);

            /*@ assert \forall integer k;
                  0 <= k && k < even_count ==>
                    IsEven(evenList[k]) && InArray{Pre}(arr, arr_len, evenList[k]);
            */

            /*@ assert \forall integer k;
                  0 <= k && k < i && IsEven(arr[k]) ==>
                    InArray{Here}(evenList, even_count, arr[k]);
            */

            /*@ assert \forall integer k;
                  0 <= k && k < i + 1 && IsEven(arr[k]) ==>
                    InArray{Here}(evenList, even_count, arr[k]);
            */
        }
    }

    /*@ assert \forall integer k;
          0 <= k && k < arr_len ==> arr[k] == \at(arr[k], Pre);
    */

    /*@ assert \forall integer k;
          0 <= k && k < even_count ==>
            IsEven(evenList[k]) && InArray{Pre}(arr, arr_len, evenList[k]);
    */

    /*@ assert \forall integer k;
          0 <= k && k < arr_len && IsEven(arr[k]) ==>
            InArray{Here}(evenList, even_count, arr[k]);
    */

    /*@ assert \forall integer k;
          0 <= k && k < arr_len && IsEven(\at(arr[k], Pre)) ==>
            InArray{Here}(evenList, even_count, \at(arr[k], Pre));
    */

    return even_count;
}