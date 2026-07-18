/*@
  requires length > 0;
  requires \valid_read(a + (0 .. length - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> (\forall integer i, j; 0 <= i && i < j && j < length ==> a[i] <= a[j]);
  ensures \result == 0 ==> (\exists integer i, j; 0 <= i && i < j && j < length && a[i] > a[j]);
*/
int IsSorted(const int *a, int length) {
  int sorted = 1;
  int i = 0;

  /*@
    loop invariant 0 <= i && i <= length - 1;
    loop invariant sorted == 0 || sorted == 1;
    loop invariant (sorted != 0) <==> (\forall integer k, l; 0 <= k && k < l && l <= i ==> a[k] <= a[l]);
    loop invariant sorted == 0 ==> (\exists integer k; 0 <= k && k < i && a[k] > a[k + 1]);
    loop assigns i, sorted;
    loop variant (length - 1) - i;
  */
  while (i < length - 1 && sorted != 0) {
    if (a[i] > a[i + 1]) {
      sorted = 0;
    }
    i++;
  }

  return sorted;
}