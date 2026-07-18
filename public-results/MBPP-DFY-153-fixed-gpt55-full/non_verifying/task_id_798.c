#include <limits.h>

/*@
  axiomatic SumToModel {
    logic integer sumTo_model{L}(int *a, integer n);

    axiom sumTo_model_zero{L}:
      \forall int *a;
        sumTo_model{L}(a, 0) == 0;

    axiom sumTo_model_step{L}:
      \forall int *a, integer n;
        n > 0 && \valid_read{L}(a + (0 .. n - 1)) ==>
        sumTo_model{L}(a, n) ==
        sumTo_model{L}(a, n - 1) + \at(a[n - 1], L);
  }
*/

/*@
  requires a != \null;
  requires 0 <= n;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  requires \forall integer k;
            0 <= k && k <= n ==>
            INT_MIN <= sumTo_model(a, k) && sumTo_model(a, k) <= INT_MAX;
  assigns \nothing;
  ensures \result == sumTo_model(a, n);
*/
int sumTo(int *a, int n) {
  if (n == 0) {
    //@ assert sumTo_model(a, 0) == 0;
    return 0;
  } else {
    //@ assert n > 0;
    //@ assert 0 <= n - 1;
    //@ assert n - 1 < n;
    //@ assert n == 1 || \valid_read(a + (0 .. n - 2));
    //@ assert n - 1 == 0 || \valid_read(a + (0 .. n - 2));
    //@ assert \forall integer k; 0 <= k && k <= n - 1 ==> INT_MIN <= sumTo_model(a, k) && sumTo_model(a, k) <= INT_MAX;
    int tmp = sumTo(a, n - 1);
    //@ assert tmp == sumTo_model(a, n - 1);
    //@ assert \valid_read(a + (0 .. n - 1));
    //@ assert sumTo_model(a, n) == sumTo_model(a, n - 1) + a[n - 1];
    //@ assert (integer)tmp + (integer)a[n - 1] == sumTo_model(a, n);
    //@ assert INT_MIN <= sumTo_model(a, n);
    //@ assert sumTo_model(a, n) <= INT_MAX;
    //@ assert INT_MIN <= (integer)tmp + (integer)a[n - 1];
    //@ assert (integer)tmp + (integer)a[n - 1] <= INT_MAX;
    return tmp + a[n - 1];
  }
}

/*@
  requires a != \null;
  requires 0 <= length;
  requires length == 0 || \valid_read(a + (0 .. length - 1));
  requires \forall integer k;
            0 <= k && k <= length ==>
            INT_MIN <= sumTo_model(a, k) && sumTo_model(a, k) <= INT_MAX;
  assigns \nothing;
  ensures \result == sumTo_model(a, length);
*/
int ArraySum(int *a, int length) {
  int result = 0;
  int i = 0;

  //@ assert sumTo_model(a, 0) == 0;
  //@ assert result == sumTo_model(a, 0);

  /*@
    loop invariant 0 <= i;
    loop invariant i <= length;
    loop invariant length == 0 || \valid_read(a + (0 .. length - 1));
    loop invariant \forall integer k;
                   0 <= k && k <= length ==>
                   INT_MIN <= sumTo_model(a, k) && sumTo_model(a, k) <= INT_MAX;
    loop invariant result == sumTo_model(a, i);
    loop assigns i, result;
    loop variant length - i;
  */
  for (i = 0; i < length; i++) {
    //@ assert 0 <= i;
    //@ assert i < length;
    //@ assert i + 1 <= length;
    //@ assert \valid_read(a + (0 .. length - 1));
    //@ assert \valid_read(a + i);
    //@ assert \valid_read(a + (0 .. i));
    //@ assert sumTo_model(a, i + 1) == sumTo_model(a, i) + a[i];
    //@ assert (integer)result + (integer)a[i] == sumTo_model(a, i + 1);
    //@ assert INT_MIN <= sumTo_model(a, i + 1);
    //@ assert sumTo_model(a, i + 1) <= INT_MAX;
    //@ assert INT_MIN <= (integer)result + (integer)a[i];
    //@ assert (integer)result + (integer)a[i] <= INT_MAX;
    result = result + a[i];
    //@ assert result == sumTo_model(a, i + 1);
  }

  //@ assert i == length;
  //@ assert result == sumTo_model(a, length);
  return result;
}