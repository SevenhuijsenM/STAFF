/*@ predicate IsEven(integer n) = n % 2 == 0; */

/*@
  requires arr_len >= 0;
  requires arr_len == 0 || \valid_read(arr + (0 .. arr_len - 1));
  requires arr_len == 0 || \valid(out + (0 .. arr_len - 1));
  requires arr_len == 0 || \separated(arr + (0 .. arr_len - 1), out + (0 .. arr_len - 1));
  assigns out[0 .. arr_len - 1];
  ensures 0 <= \result && \result <= arr_len;
  ensures \forall integer i;
            0 <= i && i < \result ==>
              IsEven(out[i]) &&
              (\exists integer j; 0 <= j && j < arr_len && out[i] == arr[j]);
  ensures \forall integer i;
            0 <= i && i < arr_len && IsEven(arr[i]) ==>
              (\exists integer j; 0 <= j && j < \result && out[j] == arr[i]);
*/
int FindEvenNumbers(const int *arr, int arr_len, int *out)
{
    int count = 0;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= arr_len;
      loop invariant 0 <= count && count <= i;
      loop invariant \forall integer k;
              0 <= k && k < count ==>
                IsEven(out[k]) &&
                (\exists integer j; 0 <= j && j < i && out[k] == arr[j]);
      loop invariant \forall integer k;
              0 <= k && k < i && IsEven(arr[k]) ==>
                (\exists integer j; 0 <= j && j < count && out[j] == arr[k]);
      loop assigns i, count, out[0 .. arr_len - 1];
      loop variant arr_len - i;
    */
    while (i < arr_len) {
        if (arr[i] % 2 == 0) {
            //@ assert IsEven(arr[i]);
            //@ assert 0 <= count && count < arr_len;
            out[count] = arr[i];
            //@ assert out[count] == arr[i];
            count++;
        }
        i++;
    }

    return count;
}