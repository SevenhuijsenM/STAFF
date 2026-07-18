/*@
axiomatic CountIdenticalPositions_Logic {
  logic integer count_identical{L}(int const *a, int const *b, int const *c, integer n)
    reads a[0 .. n-1], b[0 .. n-1], c[0 .. n-1];

  axiom count_identical_empty{L}:
    \forall int const *a, int const *b, int const *c;
      count_identical{L}(a, b, c, 0) == 0;

  axiom count_identical_succ{L}:
    \forall int const *a, int const *b, int const *c, integer k;
      0 <= k ==>
      \valid_read{L}(a + (0 .. k)) ==>
      \valid_read{L}(b + (0 .. k)) ==>
      \valid_read{L}(c + (0 .. k)) ==>
      count_identical{L}(a, b, c, k + 1) ==
        count_identical{L}(a, b, c, k) +
        ((a[k] == b[k] && b[k] == c[k]) ? 1 : 0);

  axiom count_identical_nonnegative{L}:
    \forall int const *a, int const *b, int const *c, integer k;
      0 <= k ==>
      0 <= count_identical{L}(a, b, c, k);

  axiom count_identical_upper_bound{L}:
    \forall int const *a, int const *b, int const *c, integer k;
      0 <= k ==>
      count_identical{L}(a, b, c, k) <= k;
}
*/

/*@
  requires 0 <= n;
  requires n == 0 || \valid_read(a + (0 .. n-1));
  requires n == 0 || \valid_read(b + (0 .. n-1));
  requires n == 0 || \valid_read(c + (0 .. n-1));
  assigns \nothing;
  ensures 0 <= \result;
  ensures \result <= n;
  ensures \result == count_identical(a, b, c, n);
*/
int CountIdenticalPositions(const int *a, const int *b, const int *c, int n) {
  int count = 0;
  int i = 0;

  /*@
    loop invariant 0 <= i;
    loop invariant i <= n;
    loop invariant 0 <= count;
    loop invariant count <= i;
    loop invariant count == count_identical(a, b, c, i);
    loop assigns i, count;
    loop variant n - i;
  */
  while (i < n) {
    //@ assert 0 <= i;
    //@ assert i < n;
    //@ assert i + 1 <= n;
    //@ assert n != 0;
    //@ assert \valid_read(a + (0 .. n-1));
    //@ assert \valid_read(b + (0 .. n-1));
    //@ assert \valid_read(c + (0 .. n-1));
    //@ assert \valid_read(a + (0 .. i));
    //@ assert \valid_read(b + (0 .. i));
    //@ assert \valid_read(c + (0 .. i));

    if (a[i] == b[i] && b[i] == c[i]) {
      //@ assert a[i] == b[i];
      //@ assert b[i] == c[i];
      //@ assert (a[i] == b[i] && b[i] == c[i]) ? 1 : 0 == 1;
      //@ assert count_identical(a, b, c, i + 1) == count_identical(a, b, c, i) + 1;
      //@ assert count + 1 == count_identical(a, b, c, i + 1);
      //@ assert count < n;
      //@ assert count + 1 <= n;
      count++;
      //@ assert count == count_identical(a, b, c, i + 1);
    } else {
      //@ assert !(a[i] == b[i] && b[i] == c[i]);
      //@ assert (a[i] == b[i] && b[i] == c[i]) ? 1 : 0 == 0;
      //@ assert count_identical(a, b, c, i + 1) == count_identical(a, b, c, i);
      //@ assert count == count_identical(a, b, c, i + 1);
    }

    i++;
    //@ assert count == count_identical(a, b, c, i);
  }

  //@ assert i == n;
  //@ assert count == count_identical(a, b, c, n);
  return count;
}