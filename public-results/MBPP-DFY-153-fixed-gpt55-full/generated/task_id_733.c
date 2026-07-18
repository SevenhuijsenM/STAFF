/*@
  requires length >= 0;
  requires length == 0 || \valid_read(arr + (0 .. length-1));
  requires \forall integer i, j; 0 <= i && i < j && j < length ==> arr[i] <= arr[j];
  assigns \nothing;
  ensures \result == -1 || (0 <= \result && \result < length);
  ensures 0 <= \result && \result < length ==> arr[\result] == target;
  ensures 0 <= \result && \result < length ==> \forall integer k; 0 <= k && k < \result ==> arr[k] != target;
  ensures \result == -1 ==> \forall integer i; 0 <= i && i < length ==> arr[i] != target;
  ensures \forall integer i; 0 <= i && i < length ==> arr[i] == \old(arr[i]);
*/
int FindFirstOccurrence(const int *arr, int length, int target) {
  int index = -1;
  int i = 0;

  /*@
    loop invariant 0 <= i && i <= length;
    loop invariant index == -1;
    loop invariant \forall integer k; 0 <= k && k < i ==> arr[k] != target;
    loop invariant \forall integer k; 0 <= k && k < length ==> arr[k] == \at(arr[k], Pre);
    loop assigns i, index;
    loop variant length - i;
  */
  while (i < length) {
    //@ assert index == -1;
    //@ assert 0 <= i && i < length;

    if (arr[i] == target) {
      //@ assert \forall integer k; 0 <= k && k < i ==> arr[k] != target;
      index = i;
      //@ assert 0 <= index && index < length;
      //@ assert arr[index] == target;
      //@ assert \forall integer k; 0 <= k && k < index ==> arr[k] != target;
      break;
    }

    //@ assert arr[i] != target;

    if (arr[i] > target) {
      //@ assert index == -1;
      //@ assert \forall integer k; 0 <= k && k < i ==> arr[k] != target;
      //@ assert arr[i] != target;
      //@ assert \forall integer k; i < k && k < length ==> arr[i] <= arr[k];
      //@ assert \forall integer k; i < k && k < length ==> target < arr[k];
      //@ assert \forall integer k; i < k && k < length ==> arr[k] != target;
      //@ assert \forall integer k; i <= k && k < length ==> arr[k] != target;
      //@ assert \forall integer k; 0 <= k && k < length ==> arr[k] != target;
      break;
    }

    //@ assert index == -1;
    //@ assert arr[i] != target;
    //@ assert \forall integer k; 0 <= k && k < i ==> arr[k] != target;
    //@ assert \forall integer k; 0 <= k && k < i + 1 ==> arr[k] != target;
    i++;
  }

  //@ assert index == -1 || (0 <= index && index < length);
  //@ assert 0 <= index && index < length ==> arr[index] == target;
  //@ assert 0 <= index && index < length ==> \forall integer k; 0 <= k && k < index ==> arr[k] != target;
  //@ assert index == -1 ==> \forall integer k; 0 <= k && k < length ==> arr[k] != target;

  return index;
}