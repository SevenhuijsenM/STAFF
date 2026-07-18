/*@
  requires n >= 0;
  requires n == 0 || \valid_read(s + (0 .. n - 1));
  requires n == 0 || \valid(copy + (0 .. n - 1));
  requires n == 0 || \separated(s + (0 .. n - 1), copy + (0 .. n - 1));
  assigns copy[0 .. n - 1];
  ensures \result == copy;
  ensures \forall integer i; 0 <= i && i < n ==> \result[i] == s[i];
*/
int *DeepCopySeq(const int *s, int n, int *copy)
{
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> copy[k] == s[k];
      loop assigns i, copy[0 .. n - 1];
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        copy[i] = s[i];
    }

    return copy;
}