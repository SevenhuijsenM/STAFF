#include <limits.h>

/*@
  predicate fits_int(integer x) =
    INT_MIN <= x && x <= INT_MAX;
*/

/*@
axiomatic SumNegativesToModel {
  logic integer sumNegativesTo_model{L}(int *a, integer n)
    reads a[0 .. n - 1];

  axiom sumNegativesTo_model_zero{L}:
    \forall int *a;
      sumNegativesTo_model{L}(a, 0) == 0;

  axiom sumNegativesTo_model_step_negative{L}:
    \forall int *a, integer n;
      n > 0 && \at(a[n - 1], L) < 0 ==>
        sumNegativesTo_model{L}(a, n) ==
        sumNegativesTo_model{L}(a, n - 1) + \at(a[n - 1], L);

  axiom sumNegativesTo_model_step_nonnegative{L}:
    \forall int *a, integer n;
      n > 0 && 0 <= \at(a[n - 1], L) ==>
        sumNegativesTo_model{L}(a, n) ==
        sumNegativesTo_model{L}(a, n - 1);

  axiom sumNegativesTo_model_index_negative{L}:
    \forall int *a, integer i;
      0 <= i && \at(a[i], L) < 0 ==>
        sumNegativesTo_model{L}(a, i + 1) ==
        sumNegativesTo_model{L}(a, i) + \at(a[i], L);

  axiom sumNegativesTo_model_index_nonnegative{L}:
    \forall int *a, integer i;
      0 <= i && 0 <= \at(a[i], L) ==>
        sumNegativesTo_model{L}(a, i + 1) ==
        sumNegativesTo_model{L}(a, i);
}
*/

/*@
  requires 0 <= n;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  requires \forall integer k;
            0 <= k && k <= n ==> fits_int(sumNegativesTo_model(a, k));
  assigns \nothing;
  ensures \result == sumNegativesTo_model(a, n);
  decreases n;
*/
int sumNegativesTo(int *a, int n)
{
  if (n == 0) {
    //@ assert sumNegativesTo_model(a, 0) == 0;
    return 0;
  } else {
    //@ assert 0 < n;
    //@ assert 0 <= n - 1;
    //@ assert n - 1 < n;
    //@ assert n - 1 <= n;
    //@ assert n - 1 == 0 || \valid_read(a + (0 .. (n - 1) - 1));
    //@ assert \forall integer k; 0 <= k && k <= n - 1 ==> fits_int(sumNegativesTo_model(a, k));
    int prefix = sumNegativesTo(a, n - 1);

    //@ assert prefix == sumNegativesTo_model(a, n - 1);
    //@ assert \valid_read(a + (n - 1));

    if (a[n - 1] < 0) {
      //@ assert sumNegativesTo_model(a, n) == sumNegativesTo_model(a, n - 1) + a[n - 1];
      //@ assert sumNegativesTo_model(a, n) == prefix + a[n - 1];
      //@ assert fits_int(sumNegativesTo_model(a, n));
      //@ assert INT_MIN <= prefix + a[n - 1];
      //@ assert prefix + a[n - 1] <= INT_MAX;
      return prefix + a[n - 1];
    } else {
      //@ assert 0 <= a[n - 1];
      //@ assert sumNegativesTo_model(a, n) == sumNegativesTo_model(a, n - 1);
      //@ assert sumNegativesTo_model(a, n) == prefix;
      return prefix;
    }
  }
}

/*@
  requires 0 <= length;
  requires length == 0 || \valid_read(a + (0 .. length - 1));
  requires \forall integer k;
            0 <= k && k <= length ==> fits_int(sumNegativesTo_model(a, k));
  assigns \nothing;
  ensures \result == sumNegativesTo_model(a, length);
*/
int SumOfNegatives(int *a, int length)
{
  int result = 0;
  int i;

  //@ assert sumNegativesTo_model(a, 0) == 0;

  /*@
    loop invariant 0 <= i;
    loop invariant i <= length;
    loop invariant result == sumNegativesTo_model(a, i);
    loop invariant length == 0 || \valid_read(a + (0 .. length - 1));
    loop invariant \forall integer k;
                    0 <= k && k <= length ==> fits_int(sumNegativesTo_model(a, k));
    loop assigns i, result;
    loop variant length - i;
  */
  for (i = 0; i < length; i++) {
    //@ assert 0 <= i;
    //@ assert i < length;
    //@ assert 0 <= i + 1;
    //@ assert i + 1 <= length;
    //@ assert \valid_read(a + i);

    if (a[i] < 0) {
      //@ assert sumNegativesTo_model(a, i + 1) == sumNegativesTo_model(a, i) + a[i];
      //@ assert sumNegativesTo_model(a, i + 1) == result + a[i];
      //@ assert fits_int(sumNegativesTo_model(a, i + 1));
      //@ assert INT_MIN <= result + a[i];
      //@ assert result + a[i] <= INT_MAX;
      result = result + a[i];
      //@ assert result == sumNegativesTo_model(a, i + 1);
    } else {
      //@ assert 0 <= a[i];
      //@ assert sumNegativesTo_model(a, i + 1) == sumNegativesTo_model(a, i);
      //@ assert result == sumNegativesTo_model(a, i + 1);
    }
  }

  //@ assert i == length;
  //@ assert result == sumNegativesTo_model(a, length);
  return result;
}