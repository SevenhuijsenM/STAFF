/*@
  requires 1 <= k && k <= len;
  requires \valid_read(arr + (0 .. len - 1));
  assigns \nothing;
  ensures \result == arr[k - 1];
*/
int KthElement(const int *arr, int len, int k) {
  return arr[k - 1];
}