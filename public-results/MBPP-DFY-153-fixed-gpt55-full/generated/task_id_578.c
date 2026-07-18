#include <limits.h>

/*@
  requires s1 != \null;
  requires s2 != \null;
  requires s3 != \null;
  requires r != \null;
  requires 0 <= n;
  requires n <= INT_MAX / 3;
  requires n == 0 || \valid_read(s1 + (0 .. n - 1));
  requires n == 0 || \valid_read(s2 + (0 .. n - 1));
  requires n == 0 || \valid_read(s3 + (0 .. n - 1));
  requires n == 0 || \valid(r + (0 .. 3 * n - 1));
  requires \separated(r + (0 .. 3 * n - 1), s1 + (0 .. n - 1));
  requires \separated(r + (0 .. 3 * n - 1), s2 + (0 .. n - 1));
  requires \separated(r + (0 .. 3 * n - 1), s3 + (0 .. n - 1));
  assigns r[0 .. 3 * n - 1];
  ensures \result == 3 * n;
  ensures \forall integer i; 0 <= i && i < n ==> r[3 * i] == \old(s1[i]);
  ensures \forall integer i; 0 <= i && i < n ==> r[3 * i + 1] == \old(s2[i]);
  ensures \forall integer i; 0 <= i && i < n ==> r[3 * i + 2] == \old(s3[i]);
*/
int Interleave(const int *s1, const int *s2, const int *s3, int n, int *r)
{
    int i = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> r[3 * k] == s1[k];
      loop invariant \forall integer k; 0 <= k && k < i ==> r[3 * k + 1] == s2[k];
      loop invariant \forall integer k; 0 <= k && k < i ==> r[3 * k + 2] == s3[k];
      loop assigns i, r[0 .. 3 * n - 1];
      loop variant n - i;
    */
    while (i < n) {
        r[3 * i] = s1[i];
        r[3 * i + 1] = s2[i];
        r[3 * i + 2] = s3[i];
        i++;
    }

    return 3 * n;
}