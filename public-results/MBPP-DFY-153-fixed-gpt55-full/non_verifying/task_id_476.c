#include <limits.h>

/*@
  axiomatic MinMaxLogic {
    logic integer Min_logic{L}(int *a, integer n) reads a[0 .. n-1];
    logic integer Max_logic{L}(int *a, integer n) reads a[0 .. n-1];

    axiom Min_logic_base{L}:
      \forall int *a;
        \valid_read{L}(a + (0 .. 0)) ==>
          Min_logic{L}(a, 1) == \at(a[0], L);

    axiom Min_logic_step{L}:
      \forall int *a, integer n;
        n > 1 && \valid_read{L}(a + (0 .. n-1)) ==>
          Min_logic{L}(a, n) ==
            ((\at(a[n-1], L) <= Min_logic{L}(a, n-1)) ?
              \at(a[n-1], L) : Min_logic{L}(a, n-1));

    axiom Min_logic_step_take_last{L}:
      \forall int *a, integer n;
        n > 1 && \valid_read{L}(a + (0 .. n-1)) &&
        \at(a[n-1], L) <= Min_logic{L}(a, n-1) ==>
          Min_logic{L}(a, n) == \at(a[n-1], L);

    axiom Min_logic_step_keep_prefix_strict{L}:
      \forall int *a, integer n;
        n > 1 && \valid_read{L}(a + (0 .. n-1)) &&
        \at(a[n-1], L) > Min_logic{L}(a, n-1) ==>
          Min_logic{L}(a, n) == Min_logic{L}(a, n-1);

    axiom Min_logic_step_keep_prefix{L}:
      \forall int *a, integer n;
        n > 1 && \valid_read{L}(a + (0 .. n-1)) &&
        \at(a[n-1], L) >= Min_logic{L}(a, n-1) ==>
          Min_logic{L}(a, n) == Min_logic{L}(a, n-1);

    axiom Max_logic_base{L}:
      \forall int *a;
        \valid_read{L}(a + (0 .. 0)) ==>
          Max_logic{L}(a, 1) == \at(a[0], L);

    axiom Max_logic_step{L}:
      \forall int *a, integer n;
        n > 1 && \valid_read{L}(a + (0 .. n-1)) ==>
          Max_logic{L}(a, n) ==
            ((\at(a[n-1], L) >= Max_logic{L}(a, n-1)) ?
              \at(a[n-1], L) : Max_logic{L}(a, n-1));

    axiom Max_logic_step_take_last{L}:
      \forall int *a, integer n;
        n > 1 && \valid_read{L}(a + (0 .. n-1)) &&
        \at(a[n-1], L) >= Max_logic{L}(a, n-1) ==>
          Max_logic{L}(a, n) == \at(a[n-1], L);

    axiom Max_logic_step_keep_prefix_strict{L}:
      \forall int *a, integer n;
        n > 1 && \valid_read{L}(a + (0 .. n-1)) &&
        \at(a[n-1], L) < Max_logic{L}(a, n-1) ==>
          Max_logic{L}(a, n) == Max_logic{L}(a, n-1);

    axiom Max_logic_step_keep_prefix{L}:
      \forall int *a, integer n;
        n > 1 && \valid_read{L}(a + (0 .. n-1)) &&
        \at(a[n-1], L) <= Max_logic{L}(a, n-1) ==>
          Max_logic{L}(a, n) == Max_logic{L}(a, n-1);

    axiom Min_logic_lower_bound{L}:
      \forall int *a, integer n, integer k;
        n > 0 && \valid_read{L}(a + (0 .. n-1)) &&
        0 <= k && k < n ==>
          Min_logic{L}(a, n) <= \at(a[k], L);

    axiom Max_logic_upper_bound{L}:
      \forall int *a, integer n, integer k;
        n > 0 && \valid_read{L}(a + (0 .. n-1)) &&
        0 <= k && k < n ==>
          \at(a[k], L) <= Max_logic{L}(a, n);

    axiom Min_logic_member{L}:
      \forall int *a, integer n;
        n > 0 && \valid_read{L}(a + (0 .. n-1)) ==>
          \exists integer k; 0 <= k && k < n && Min_logic{L}(a, n) == \at(a[k], L);

    axiom Max_logic_member{L}:
      \forall int *a, integer n;
        n > 0 && \valid_read{L}(a + (0 .. n-1)) ==>
          \exists integer k; 0 <= k && k < n && Max_logic{L}(a, n) == \at(a[k], L);

    axiom Min_logic_le_Max_logic{L}:
      \forall int *a, integer n;
        n > 0 && \valid_read{L}(a + (0 .. n-1)) ==>
          Min_logic{L}(a, n) <= Max_logic{L}(a, n);
  }
*/

/*@
  requires n > 0;
  requires \valid_read(a + (0 .. n-1));
  assigns \nothing;
  decreases n;
  ensures \result == Min_logic(a, n);
  ensures \forall integer k; 0 <= k && k < n ==> \result <= a[k];
  ensures \exists integer k; 0 <= k && k < n && \result == a[k];
*/
int Min(int *a, int n) {
  if (n == 1) {
    //@ assert \valid_read(a + (0 .. 0));
    //@ assert Min_logic(a, 1) == a[0];
    return a[0];
  } else {
    //@ assert n > 1;
    //@ assert \valid_read(a + (0 .. n-2));
    int minPrefix = Min(a, n - 1);
    //@ assert minPrefix == Min_logic(a, n - 1);
    //@ assert \valid_read(a + (0 .. n-1));

    if (a[n - 1] <= minPrefix) {
      //@ assert a[n - 1] <= Min_logic(a, n - 1);
      //@ assert Min_logic(a, n) == a[n - 1];
      return a[n - 1];
    } else {
      //@ assert a[n - 1] > Min_logic(a, n - 1);
      //@ assert Min_logic(a, n) == Min_logic(a, n - 1);
      int r = Min(a, n - 1);
      //@ assert r == Min_logic(a, n - 1);
      //@ assert r == Min_logic(a, n);
      return r;
    }
  }
}

/*@
  requires n > 0;
  requires \valid_read(a + (0 .. n-1));
  assigns \nothing;
  decreases n;
  ensures \result == Max_logic(a, n);
  ensures \forall integer k; 0 <= k && k < n ==> a[k] <= \result;
  ensures \exists integer k; 0 <= k && k < n && \result == a[k];
*/
int Max(int *a, int n) {
  if (n == 1) {
    //@ assert \valid_read(a + (0 .. 0));
    //@ assert Max_logic(a, 1) == a[0];
    return a[0];
  } else {
    //@ assert n > 1;
    //@ assert \valid_read(a + (0 .. n-2));
    int maxPrefix = Max(a, n - 1);
    //@ assert maxPrefix == Max_logic(a, n - 1);
    //@ assert \valid_read(a + (0 .. n-1));

    if (a[n - 1] >= maxPrefix) {
      //@ assert a[n - 1] >= Max_logic(a, n - 1);
      //@ assert Max_logic(a, n) == a[n - 1];
      return a[n - 1];
    } else {
      //@ assert a[n - 1] < Max_logic(a, n - 1);
      //@ assert Max_logic(a, n) == Max_logic(a, n - 1);
      int r = Max(a, n - 1);
      //@ assert r == Max_logic(a, n - 1);
      //@ assert r == Max_logic(a, n);
      return r;
    }
  }
}

/*@
  requires n > 0;
  requires \valid_read(a + (0 .. n-1));
  requires INT_MIN <= Min_logic(a, n) + Max_logic(a, n);
  requires Min_logic(a, n) + Max_logic(a, n) <= INT_MAX;
  assigns \nothing;
  ensures \result == Max_logic(a, n) + Min_logic(a, n);
*/
int SumMinMax(int *a, int n) {
  int minVal = a[0];
  int maxVal = a[0];
  int i;

  //@ assert \valid_read(a + (0 .. 0));
  //@ assert Min_logic(a, 1) == a[0];
  //@ assert Max_logic(a, 1) == a[0];

  /*@
    loop invariant 1 <= i;
    loop invariant i <= n;
    loop invariant \valid_read(a + (0 .. n-1));
    loop invariant minVal == Min_logic(a, i);
    loop invariant maxVal == Max_logic(a, i);
    loop invariant minVal <= maxVal;
    loop invariant \forall integer k; 0 <= k && k < i ==> minVal <= a[k];
    loop invariant \forall integer k; 0 <= k && k < i ==> a[k] <= maxVal;
    loop assigns i, minVal, maxVal;
    loop variant n - i;
  */
  for (i = 1; i < n; i++) {
    int oldMin = minVal;
    int oldMax = maxVal;

    //@ assert 1 <= i;
    //@ assert i < n;
    //@ assert oldMin == Min_logic(a, i);
    //@ assert oldMax == Max_logic(a, i);
    //@ assert \valid_read(a + (0 .. i));

    if (a[i] < minVal) {
      //@ assert a[i] < oldMin;
      //@ assert a[i] <= Min_logic(a, i);
      //@ assert a[i] < oldMax;
      minVal = a[i];
      //@ assert minVal == a[i];
      //@ assert Min_logic(a, i + 1) == a[i];
      //@ assert Max_logic(a, i + 1) == oldMax;
      //@ assert maxVal == oldMax;
    } else if (a[i] > maxVal) {
      //@ assert a[i] >= oldMin;
      //@ assert oldMin <= oldMax;
      //@ assert a[i] > oldMin;
      //@ assert a[i] > oldMax;
      //@ assert a[i] > Min_logic(a, i);
      //@ assert a[i] >= Max_logic(a, i);
      maxVal = a[i];
      //@ assert maxVal == a[i];
      //@ assert Min_logic(a, i + 1) == oldMin;
      //@ assert Max_logic(a, i + 1) == a[i];
      //@ assert minVal == oldMin;
    } else {
      //@ assert a[i] >= oldMin;
      //@ assert a[i] <= oldMax;
      //@ assert a[i] >= Min_logic(a, i);
      //@ assert a[i] <= Max_logic(a, i);
      //@ assert Min_logic(a, i + 1) == oldMin;
      //@ assert Max_logic(a, i + 1) == oldMax;
      //@ assert minVal == oldMin;
      //@ assert maxVal == oldMax;
    }

    //@ assert minVal == Min_logic(a, i + 1);
    //@ assert maxVal == Max_logic(a, i + 1);
    //@ assert minVal <= maxVal;
  }

  //@ assert i == n;
  //@ assert minVal == Min_logic(a, n);
  //@ assert maxVal == Max_logic(a, n);
  //@ assert INT_MIN <= minVal + maxVal;
  //@ assert minVal + maxVal <= INT_MAX;

  int sum = minVal + maxVal;
  //@ assert sum == Min_logic(a, n) + Max_logic(a, n);
  //@ assert sum == Max_logic(a, n) + Min_logic(a, n);
  return sum;
}