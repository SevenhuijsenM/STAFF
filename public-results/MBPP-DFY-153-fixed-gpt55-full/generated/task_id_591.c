/*@
  requires length > 0;
  requires \valid(a + (0 .. length - 1));
  assigns a[0 .. length - 1];
  ensures a[0] == \old(a[length - 1]);
  ensures a[length - 1] == \old(a[0]);
  ensures \forall integer k; 1 <= k && k < length - 1 ==> a[k] == \old(a[k]);
*/
void SwapFirstAndLast(int *a, int length)
{
    int temp = a[0];
    a[0] = a[length - 1];
    a[length - 1] = temp;
}