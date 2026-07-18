#include <stddef.h>

/*@
  predicate char_in{L}(char c, char const *a, integer n) =
    \exists integer j; 0 <= j && j < n && \at(a[j], L) == c;
*/

/*@
  axiomatic CharInProperties {
    axiom char_in_monotonic{L}:
      \forall char c, char const *a, integer n, integer m;
        0 <= n && n <= m && char_in(c, a, n) ==> char_in(c, a, m);
  }
*/

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result == 1 ==> char_in(c, a, n);
  ensures \result == 0 ==> ! char_in(c, a, n);
*/
int contains(const char *a, int n, char c)
{
    int i;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> a[k] != c;
      loop assigns i;
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        if (a[i] == c) {
            //@ assert 0 <= i;
            //@ assert i < n;
            //@ assert a[i] == c;
            //@ assert \exists integer j; 0 <= j && j < n && a[j] == c;
            //@ assert char_in(c, a, n);
            return 1;
        }
    }

    //@ assert i == n;
    //@ assert \forall integer k; 0 <= k && k < n ==> a[k] != c;
    //@ assert ! \exists integer j; 0 <= j && j < n && a[j] == c;
    //@ assert ! char_in(c, a, n);
    return 0;
}

/*@
  requires n1 >= 0;
  requires n2 >= 0;
  requires n1 == 0 || \valid_read(s1 + (0 .. n1 - 1));
  requires n2 == 0 || \valid_read(s2 + (0 .. n2 - 1));
  requires n1 == 0 || \valid(v + (0 .. n1 - 1));
  requires n1 == 0 || \separated(v + (0 .. n1 - 1), s1 + (0 .. n1 - 1));
  requires n1 == 0 || n2 == 0 || \separated(v + (0 .. n1 - 1), s2 + (0 .. n2 - 1));
  assigns v[0 .. n1 - 1];
  ensures 0 <= \result;
  ensures \result <= n1;
  ensures \forall integer i; 0 <= i && i < \result ==> char_in(v[i], s1, n1);
  ensures \forall integer i; 0 <= i && i < \result ==> ! char_in(v[i], s2, n2);
  ensures \forall integer i; 0 <= i && i < n1 ==> char_in(s1[i], s2, n2) || char_in(s1[i], v, \result);
*/
int RemoveChars(const char *s1, int n1, const char *s2, int n2, char *v)
{
    int vp = 0;
    int in_s2 = 0;
    int i;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= n1;
      loop invariant 0 <= vp;
      loop invariant vp <= i;
      loop invariant \forall integer k; 0 <= k && k < vp ==> char_in(v[k], s1, n1);
      loop invariant \forall integer k; 0 <= k && k < vp ==> ! char_in(v[k], s2, n2);
      loop invariant \forall integer k; 0 <= k && k < i ==> char_in(s1[k], s2, n2) || char_in(s1[k], v, vp);
      loop assigns i, vp, in_s2, v[0 .. n1 - 1];
      loop variant n1 - i;
    */
    for (i = 0; i < n1; i++) {
        //@ assert 0 <= i;
        //@ assert i < n1;
        //@ assert n1 > 0;
        //@ assert s1[i] == s1[i];
        //@ assert \exists integer j; 0 <= j && j < n1 && s1[j] == s1[i];
        //@ assert char_in(s1[i], s1, n1);

        in_s2 = contains(s2, n2, s1[i]);

        //@ assert in_s2 == 0 || in_s2 == 1;

        if (in_s2 == 0) {
            //@ assert ! char_in(s1[i], s2, n2);
            //@ assert 0 <= vp;
            //@ assert vp <= i;
            //@ assert vp < n1;
            //@ assert \valid(v + vp);

            v[vp] = s1[i];

            //@ assert v[vp] == s1[i];
            //@ assert char_in(v[vp], s1, n1);
            //@ assert ! char_in(v[vp], s2, n2);
            //@ assert \exists integer j; 0 <= j && j < vp + 1 && v[j] == s1[i];
            //@ assert char_in(s1[i], v, vp + 1);
            //@ assert \forall integer k; 0 <= k && k < vp ==> char_in(v[k], s1, n1);
            //@ assert \forall integer k; 0 <= k && k < vp ==> ! char_in(v[k], s2, n2);
            //@ assert \forall integer k; 0 <= k && k < vp + 1 ==> char_in(v[k], s1, n1);
            //@ assert \forall integer k; 0 <= k && k < vp + 1 ==> ! char_in(v[k], s2, n2);
            //@ assert \forall integer k; 0 <= k && k < i && char_in(s1[k], v, vp) ==> char_in(s1[k], v, vp + 1);
            //@ assert \forall integer k; 0 <= k && k < i ==> char_in(s1[k], s2, n2) || char_in(s1[k], v, vp + 1);
            //@ assert \forall integer k; 0 <= k && k < i + 1 ==> char_in(s1[k], s2, n2) || char_in(s1[k], v, vp + 1);

            vp++;

            //@ assert 0 <= vp;
            //@ assert vp <= i + 1;
            //@ assert char_in(s1[i], v, vp);
            //@ assert \forall integer k; 0 <= k && k < vp ==> char_in(v[k], s1, n1);
            //@ assert \forall integer k; 0 <= k && k < vp ==> ! char_in(v[k], s2, n2);
            //@ assert \forall integer k; 0 <= k && k < i + 1 ==> char_in(s1[k], s2, n2) || char_in(s1[k], v, vp);
        } else {
            //@ assert in_s2 == 1;
            //@ assert char_in(s1[i], s2, n2);
            //@ assert \forall integer k; 0 <= k && k < i ==> char_in(s1[k], s2, n2) || char_in(s1[k], v, vp);
            //@ assert \forall integer k; 0 <= k && k < i + 1 ==> char_in(s1[k], s2, n2) || char_in(s1[k], v, vp);
        }
    }

    //@ assert i == n1;
    //@ assert 0 <= vp;
    //@ assert vp <= n1;
    return vp;
}