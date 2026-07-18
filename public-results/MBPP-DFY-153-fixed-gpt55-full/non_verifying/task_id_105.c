#include <stdbool.h>
#include <limits.h>

/*@
axiomatic CountTo {
  logic integer countTo_logic{L}(bool *a, integer n) reads a[0 .. n - 1];

  axiom countTo_zero{L}:
    \forall bool *a;
      countTo_logic{L}(a, 0) == 0;

  axiom countTo_step{L}:
    \forall bool *a, integer n;
      0 < n && \valid_read(a + (0 .. n - 1)) ==>
        countTo_logic{L}(a, n) ==
          countTo_logic{L}(a, n - 1) + (a[n - 1] != 0 ? 1 : 0);

  axiom countTo_succ{L}:
    \forall bool *a, integer i;
      0 <= i && \valid_read(a + (0 .. i)) ==>
        countTo_logic{L}(a, i + 1) ==
          countTo_logic{L}(a, i) + (a[i] != 0 ? 1 : 0);

  axiom countTo_step_true{L}:
    \forall bool *a, integer n;
      0 < n && \valid_read(a + (0 .. n - 1)) && a[n - 1] != 0 ==>
        countTo_logic{L}(a, n) == countTo_logic{L}(a, n - 1) + 1;

  axiom countTo_step_false{L}:
    \forall bool *a, integer n;
      0 < n && \valid_read(a + (0 .. n - 1)) && a[n - 1] == 0 ==>
        countTo_logic{L}(a, n) == countTo_logic{L}(a, n - 1);

  axiom countTo_succ_true{L}:
    \forall bool *a, integer i;
      0 <= i && \valid_read(a + (0 .. i)) && a[i] != 0 ==>
        countTo_logic{L}(a, i + 1) == countTo_logic{L}(a, i) + 1;

  axiom countTo_succ_false{L}:
    \forall bool *a, integer i;
      0 <= i && \valid_read(a + (0 .. i)) && a[i] == 0 ==>
        countTo_logic{L}(a, i + 1) == countTo_logic{L}(a, i);

  axiom countTo_nonnegative{L}:
    \forall bool *a, integer n;
      0 <= n && (n == 0 || \valid_read(a + (0 .. n - 1))) ==>
        0 <= countTo_logic{L}(a, n);

  axiom countTo_upper_bound{L}:
    \forall bool *a, integer n;
      0 <= n && (n == 0 || \valid_read(a + (0 .. n - 1))) ==>
        countTo_logic{L}(a, n) <= n;
}
*/

/*@
  requires 0 <= n;
  requires n <= INT_MAX;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  assigns \nothing;
  decreases n;
  ensures \result == countTo_logic(a, n);
  ensures 0 <= \result;
  ensures \result <= n;
*/
int countTo(bool *a, int n)
{
  if (n == 0) {
    //@ assert countTo_logic(a, 0) == 0;
    return 0;
  } else {
    //@ assert 0 < n;
    //@ assert \valid_read(a + (0 .. n - 1));
    //@ assert 0 <= n - 1;
    //@ assert n - 1 <= INT_MAX;
    //@ assert n - 1 == 0 || \valid_read(a + (0 .. n - 2));
    int prev = countTo(a, n - 1);
    //@ assert prev == countTo_logic(a, n - 1);
    //@ assert 0 <= prev;
    //@ assert prev <= n - 1;
    //@ assert \valid_read(a + (n - 1));
    if (a[n - 1]) {
      //@ assert a[n - 1] != 0;
      //@ assert prev < INT_MAX;
      //@ assert countTo_logic(a, n) == countTo_logic(a, n - 1) + 1;
      //@ assert prev + 1 == countTo_logic(a, n);
      //@ assert 0 <= prev + 1;
      //@ assert prev + 1 <= n;
      return prev + 1;
    } else {
      //@ assert a[n - 1] == 0;
      //@ assert countTo_logic(a, n) == countTo_logic(a, n - 1);
      //@ assert prev == countTo_logic(a, n);
      //@ assert prev <= n;
      return prev;
    }
  }
}

/*@
  requires 0 <= length;
  requires length <= INT_MAX;
  requires length == 0 || \valid_read(a + (0 .. length - 1));
  assigns \nothing;
  ensures \result == countTo_logic(a, length);
  ensures 0 <= \result;
  ensures \result <= length;
*/
int CountTrue(bool *a, int length)
{
  int result = 0;
  int i = 0;

  /*@
    loop invariant 0 <= i;
    loop invariant i <= length;
    loop invariant 0 <= length;
    loop invariant length <= INT_MAX;
    loop invariant length == 0 || \valid_read(a + (0 .. length - 1));
    loop invariant i == 0 || \valid_read(a + (0 .. i - 1));
    loop invariant i < length ==> \valid_read(a + (0 .. i));
    loop invariant result == countTo_logic(a, i);
    loop invariant 0 <= result;
    loop invariant result <= i;
    loop assigns i, result;
    loop variant length - i;
  */
  for (; i < length; i++) {
    //@ assert 0 <= i;
    //@ assert i < length;
    //@ assert i < INT_MAX;
    //@ assert \valid_read(a + i);
    //@ assert \valid_read(a + (0 .. i));
    //@ assert countTo_logic(a, i + 1) == countTo_logic(a, i) + (a[i] != 0 ? 1 : 0);
    if (a[i]) {
      //@ assert a[i] != 0;
      //@ assert result == countTo_logic(a, i);
      //@ assert result <= i;
      //@ assert result < INT_MAX;
      //@ assert countTo_logic(a, i + 1) == countTo_logic(a, i) + 1;
      result = result + 1;
      //@ assert result == countTo_logic(a, i) + 1;
      //@ assert result == countTo_logic(a, i + 1);
    } else {
      //@ assert a[i] == 0;
      //@ assert result == countTo_logic(a, i);
      //@ assert countTo_logic(a, i + 1) == countTo_logic(a, i);
      //@ assert result == countTo_logic(a, i + 1);
    }
    //@ assert result == countTo_logic(a, i + 1);
    //@ assert 0 <= result;
    //@ assert result <= i + 1;
  }

  //@ assert i == length;
  //@ assert result == countTo_logic(a, length);
  return result;
}