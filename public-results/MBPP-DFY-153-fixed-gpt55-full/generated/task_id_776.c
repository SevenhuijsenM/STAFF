#include <limits.h>

/*@ predicate IsVowelChar(char c) =
      c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
      c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U';
*/

/*@
  axiomatic CountVowelNeighbors_Model {
    logic integer CountVowelNeighbors_prefix{L}(char *s, integer n, integer k)
      reads s[0 .. n-1];

    axiom CountVowelNeighbors_prefix_base{L}:
      \forall char *s, integer n, integer k;
        k <= 1 ==> CountVowelNeighbors_prefix(s, n, k) == 0;

    axiom CountVowelNeighbors_prefix_step_hit{L}:
      \forall char *s, integer n, integer k;
        0 <= n &&
        2 <= k &&
        k <= n - 1 &&
        IsVowelChar(s[k - 2]) &&
        IsVowelChar(s[k]) ==>
          CountVowelNeighbors_prefix(s, n, k) ==
          CountVowelNeighbors_prefix(s, n, k - 1) + 1;

    axiom CountVowelNeighbors_prefix_step_miss{L}:
      \forall char *s, integer n, integer k;
        0 <= n &&
        2 <= k &&
        k <= n - 1 &&
        (!IsVowelChar(s[k - 2]) || !IsVowelChar(s[k])) ==>
          CountVowelNeighbors_prefix(s, n, k) ==
          CountVowelNeighbors_prefix(s, n, k - 1);

    axiom CountVowelNeighbors_prefix_nonnegative{L}:
      \forall char *s, integer n, integer k;
        0 <= CountVowelNeighbors_prefix(s, n, k);

    axiom CountVowelNeighbors_prefix_upper{L}:
      \forall char *s, integer n, integer k;
        0 <= n &&
        1 <= k &&
        k <= n - 1 ==>
          CountVowelNeighbors_prefix(s, n, k) <= k - 1;
  }
*/

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures IsVowelChar(c) ==> \result == 1;
  ensures !IsVowelChar(c) ==> \result == 0;
  ensures (\result != 0) <==> IsVowelChar(c);
*/
int IsVowel(char c)
{
    return c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
           c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U';
}

/*@
  requires 0 <= n;
  requires n <= INT_MAX;
  requires n == 0 || \valid_read(s + (0 .. n-1));
  assigns \nothing;
  ensures 0 <= \result;
  ensures n <= 2 ==> \result == 0;
  ensures 2 < n ==> \result <= n - 2;
  ensures \result == CountVowelNeighbors_prefix(s, n, n - 1);
*/
int CountVowelNeighbors(char *s, int n)
{
    if (n <= 2) {
        //@ assert n - 1 <= 1;
        //@ assert CountVowelNeighbors_prefix(s, n, n - 1) == 0;
        return 0;
    }

    //@ assert 2 < n;
    //@ assert n != 0;
    //@ assert \valid_read(s + (0 .. n-1));

    int count = 0;
    int i = 1;

    //@ assert CountVowelNeighbors_prefix(s, n, 1) == 0;

    /*@
      loop invariant 1 <= i;
      loop invariant i <= n - 1;
      loop invariant 0 <= count;
      loop invariant count <= i - 1;
      loop invariant count == CountVowelNeighbors_prefix(s, n, i);
      loop assigns i, count;
      loop variant n - 1 - i;
    */
    for (; i < n - 1; i++) {
        //@ assert 1 <= i;
        //@ assert i <= n - 2;
        //@ assert 0 <= i - 1;
        //@ assert i + 1 <= n - 1;
        //@ assert \valid_read(s + (i - 1));
        //@ assert \valid_read(s + (i + 1));

        int left = IsVowel(s[i - 1]);
        //@ assert (left != 0) <==> IsVowelChar(s[i - 1]);

        int right = IsVowel(s[i + 1]);
        //@ assert (right != 0) <==> IsVowelChar(s[i + 1]);

        if (left != 0 && right != 0) {
            //@ assert IsVowelChar(s[i - 1]);
            //@ assert IsVowelChar(s[i + 1]);
            //@ assert count <= i - 1;
            //@ assert count <= n - 3;
            //@ assert count < INT_MAX;
            count++;
            //@ assert count == CountVowelNeighbors_prefix(s, n, i) + 1;
            //@ assert 0 <= n;
            //@ assert 2 <= i + 1;
            //@ assert i + 1 <= n - 1;
            //@ assert IsVowelChar(s[(i + 1) - 2]);
            //@ assert IsVowelChar(s[i + 1]);
            //@ assert CountVowelNeighbors_prefix(s, n, i + 1) == CountVowelNeighbors_prefix(s, n, i) + 1;
            //@ assert count == CountVowelNeighbors_prefix(s, n, i + 1);
        } else {
            //@ assert left == 0 || right == 0;
            //@ assert !IsVowelChar(s[i - 1]) || !IsVowelChar(s[i + 1]);
            //@ assert count == CountVowelNeighbors_prefix(s, n, i);
            //@ assert 0 <= n;
            //@ assert 2 <= i + 1;
            //@ assert i + 1 <= n - 1;
            //@ assert !IsVowelChar(s[(i + 1) - 2]) || !IsVowelChar(s[i + 1]);
            //@ assert CountVowelNeighbors_prefix(s, n, i + 1) == CountVowelNeighbors_prefix(s, n, i);
            //@ assert count == CountVowelNeighbors_prefix(s, n, i + 1);
        }

        //@ assert count == CountVowelNeighbors_prefix(s, n, i + 1);
        //@ assert 0 <= count;
        //@ assert count <= i;
        //@ assert i <= n - 2;
    }

    //@ assert i == n - 1;
    //@ assert count == CountVowelNeighbors_prefix(s, n, n - 1);
    //@ assert 0 <= count;
    //@ assert count <= n - 2;
    return count;
}