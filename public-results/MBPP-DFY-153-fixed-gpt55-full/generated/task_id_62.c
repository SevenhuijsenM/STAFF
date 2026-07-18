/*@
  requires n > 0;
  requires \valid_read(s + (0 .. n - 1));
  assigns \nothing;
  ensures \forall integer i; 0 <= i && i < n ==> \result <= s[i];
  ensures \exists integer i; 0 <= i && i < n && \result == s[i];
*/
int FindSmallest(const int *s, int n)
{
  int min = s[0];

  /*@
    loop invariant 1 <= i && i <= n;
    loop invariant \forall integer k; 0 <= k && k < i ==> min <= s[k];
    loop invariant \exists integer k; 0 <= k && k < i && min == s[k];
    loop assigns i, min;
    loop variant n - i;
  */
  for (int i = 1; i < n; i++) {
    if (s[i] < min) {
      min = s[i];
    }
  }

  return min;
}