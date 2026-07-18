#include <limits.h>

/*@
  requires 0 <= s_len;
  requires 0 <= a_len;
  requires s_len <= INT_MAX - a_len;
  requires s_len == 0 || \valid_read(s + (0 .. s_len - 1));
  requires a_len == 0 || \valid_read(a + (0 .. a_len - 1));
  requires s_len + a_len == 0 || \valid(r + (0 .. s_len + a_len - 1));
  requires \separated(r + (0 .. s_len + a_len - 1), s + (0 .. s_len - 1));
  requires \separated(r + (0 .. s_len + a_len - 1), a + (0 .. a_len - 1));
  assigns r[0 .. s_len + a_len - 1];
  ensures \result == s_len + a_len;
  ensures \forall integer i; 0 <= i && i < s_len ==> r[i] == \old(s[i]);
  ensures \forall integer i; 0 <= i && i < a_len ==> r[s_len + i] == \old(a[i]);
*/
int AppendArrayToSeq(const int *s, int s_len, const int *a, int a_len, int *r)
{
    int r_len = 0;

    /*@
      loop invariant 0 <= i && i <= s_len;
      loop invariant r_len == i;
      loop invariant \forall integer j; 0 <= j && j < i ==> r[j] == s[j];
      loop assigns i, r_len, r[0 .. s_len - 1];
      loop variant s_len - i;
    */
    for (int i = 0; i < s_len; i++) {
        r[i] = s[i];
        r_len++;
    }

    /*@
      loop invariant 0 <= i && i <= a_len;
      loop invariant r_len == s_len + i;
      loop invariant \forall integer j; 0 <= j && j < s_len ==> r[j] == s[j];
      loop invariant \forall integer j; 0 <= j && j < i ==> r[s_len + j] == a[j];
      loop assigns i, r_len, r[s_len .. s_len + a_len - 1];
      loop variant a_len - i;
    */
    for (int i = 0; i < a_len; i++) {
        r[r_len] = a[i];
        r_len++;
    }

    return r_len;
}