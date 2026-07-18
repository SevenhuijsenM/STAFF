#include <limits.h>

/*@
axiomatic MinMaxLogic {
  logic integer Min_logic{L}(int *a, integer n) reads a[0 .. n-1];
  logic integer Max_logic{L}(int *a, integer n) reads a[0 .. n-1];

  axiom Min_one{L}:
    \forall int *a;
      \valid_read{L}(a) ==> Min_logic{L}(a, 1) == a[0];

  axiom Min_step{L}:
    \forall int *a, integer n;
      n > 1 && \valid_read{L}(a + (0 .. n-1)) ==>
        Min_logic{L}(a, n) ==
          (a[n-1] <= Min_logic{L}(a, n-1) ? a[n-1] : Min_logic{L}(a, n-1));

  axiom Min_lower_bound{L}:
    \forall int *a, integer n, integer k;
      n > 0 && \valid_read{L}(a + (0 .. n-1)) &&
      0 <= k && k < n ==>
        Min_logic{L}(a, n) <= a[k];

  axiom Min_is_member{L}:
    \forall int *a, integer n;
      n > 0 && \valid_read{L}(a + (0 .. n-1)) ==>
        \exists integer k; 0 <= k && k < n && Min_logic{L}(a, n) == a[k];

  axiom Max_one{L}:
    \forall int *a;
      \valid_read{L}(a) ==> Max_logic{L}(a, 1) == a[0];

  axiom Max_step{L}:
    \forall int *a, integer n;
      n > 1 && \valid_read{L}(a + (0 .. n-1)) ==>
        Max_logic{L}(a, n) ==
          (a[n-1] >= Max_logic{L}(a, n-1) ? a[n-1] : Max_logic{L}(a, n-1));

  axiom Max_upper_bound{L}:
    \forall int *a, integer n, integer k;
      n > 0 && \valid_read{L}(a + (0 .. n-1)) &&
      0 <= k && k < n ==>
        a[k] <= Max_logic{L}(a, n);

  axiom Max_is_member{L}:
    \forall int *a, integer n;
      n > 0 && \valid_read{L}(a + (0 .. n-1)) ==>
        \exists integer k; 0 <= k && k < n && Max_logic{L}(a, n) == a[k];

  axiom Min_le_Max{L}:
    \forall int *a, integer n;
      n > 0 && \valid_read{L}(a + (0 .. n-1)) ==>
        Min_logic{L}(a, n) <= Max_logic{L}(a, n);
}
*/

/*@
  requires n > 0;
  requires \valid_read(a + (0 .. n-1));
  assigns \nothing;
  ensures \result == Min_logic(a, n);
  decreases n;
*/
int Min(int *a, int n)
{
  if (n == 1) {
    //@ assert \valid_read(a);
    //@ assert Min_logic(a, 1) == a[0];
    return a[0];
  } else {
    //@ assert n > 1;
    //@ assert n - 1 > 0;
    //@ assert \valid_read(a + (0 .. n-2));
    int minPrefix = Min(a, n - 1);
    //@ assert minPrefix == Min_logic(a, n - 1);
    //@ assert Min_logic(a, n) == (a[n-1] <= Min_logic(a, n-1) ? a[n-1] : Min_logic(a, n-1));
    if (a[n - 1] <= minPrefix) {
      //@ assert a[n-1] <= Min_logic(a, n-1);
      //@ assert Min_logic(a, n) == a[n-1];
      return a[n - 1];
    } else {
      //@ assert a[n-1] > Min_logic(a, n-1);
      //@ assert Min_logic(a, n) == Min_logic(a, n-1);
      //@ assert Min_logic(a, n) == minPrefix;
      return minPrefix;
    }
  }
}

/*@
  requires n > 0;
  requires \valid_read(a + (0 .. n-1));
  assigns \nothing;
  ensures \result == Max_logic(a, n);
  decreases n;
*/
int Max(int *a, int n)
{
  if (n == 1) {
    //@ assert \valid_read(a);
    //@ assert Max_logic(a, 1) == a[0];
    return a[0];
  } else {
    //@ assert n > 1;
    //@ assert n - 1 > 0;
    //@ assert \valid_read(a + (0 .. n-2));
    int maxPrefix = Max(a, n - 1);
    //@ assert maxPrefix == Max_logic(a, n - 1);
    //@ assert Max_logic(a, n) == (a[n-1] >= Max_logic(a, n-1) ? a[n-1] : Max_logic(a, n-1));
    if (a[n - 1] >= maxPrefix) {
      //@ assert a[n-1] >= Max_logic(a, n-1);
      //@ assert Max_logic(a, n) == a[n-1];
      return a[n - 1];
    } else {
      //@ assert a[n-1] < Max_logic(a, n-1);
      //@ assert Max_logic(a, n) == Max_logic(a, n-1);
      //@ assert Max_logic(a, n) == maxPrefix;
      return maxPrefix;
    }
  }
}

/*@
  requires n > 0;
  requires \valid_read(a + (0 .. n-1));
  requires INT_MIN <= Max_logic(a, n) - Min_logic(a, n);
  requires Max_logic(a, n) - Min_logic(a, n) <= INT_MAX;
  assigns \nothing;
  ensures \result == Max_logic(a, n) - Min_logic(a, n);
*/
int DifferenceMinMax(int *a, int n)
{
  int minVal = a[0];
  int maxVal = a[0];
  int i = 1;

  //@ assert \valid_read(a);
  //@ assert Min_logic(a, 1) == a[0];
  //@ assert Max_logic(a, 1) == a[0];
  //@ assert minVal == Min_logic(a, 1);
  //@ assert maxVal == Max_logic(a, 1);
  //@ assert minVal <= maxVal;
  //@ assert \forall integer k; 0 <= k && k < 1 ==> minVal <= a[k] && a[k] <= maxVal;

  /*@
    loop invariant 1 <= i;
    loop invariant i <= n;
    loop invariant minVal <= maxVal;
    loop invariant minVal == Min_logic(a, i);
    loop invariant maxVal == Max_logic(a, i);
    loop invariant \forall integer k; 0 <= k && k < i ==> minVal <= a[k] && a[k] <= maxVal;
    loop assigns i, minVal, maxVal;
    loop variant n - i;
  */
  while (i < n) {
    int oldMin = minVal;
    int oldMax = maxVal;

    //@ assert 1 <= i;
    //@ assert i < n;
    //@ assert i + 1 <= n;
    //@ assert \valid_read(a + (0 .. i));
    //@ assert oldMin == Min_logic(a, i);
    //@ assert oldMax == Max_logic(a, i);
    //@ assert oldMin <= oldMax;

    if (a[i] < minVal) {
      minVal = a[i];
      //@ assert minVal == a[i];
      //@ assert maxVal == oldMax;
      //@ assert a[i] < oldMin;
      //@ assert a[i] <= Min_logic(a, i);
      //@ assert Min_logic(a, i + 1) == (a[i] <= Min_logic(a, i) ? a[i] : Min_logic(a, i));
      //@ assert Min_logic(a, i + 1) == a[i];
      //@ assert minVal == Min_logic(a, i + 1);
      //@ assert a[i] < oldMax;
      //@ assert a[i] < Max_logic(a, i);
      //@ assert Max_logic(a, i + 1) == (a[i] >= Max_logic(a, i) ? a[i] : Max_logic(a, i));
      //@ assert Max_logic(a, i + 1) == Max_logic(a, i);
      //@ assert maxVal == Max_logic(a, i + 1);
    } else if (a[i] > maxVal) {
      maxVal = a[i];
      //@ assert minVal == oldMin;
      //@ assert maxVal == a[i];
      //@ assert a[i] > oldMax;
      //@ assert a[i] > oldMin;
      //@ assert a[i] > Min_logic(a, i);
      //@ assert Min_logic(a, i + 1) == (a[i] <= Min_logic(a, i) ? a[i] : Min_logic(a, i));
      //@ assert Min_logic(a, i + 1) == Min_logic(a, i);
      //@ assert minVal == Min_logic(a, i + 1);
      //@ assert a[i] >= Max_logic(a, i);
      //@ assert Max_logic(a, i + 1) == (a[i] >= Max_logic(a, i) ? a[i] : Max_logic(a, i));
      //@ assert Max_logic(a, i + 1) == a[i];
      //@ assert maxVal == Max_logic(a, i + 1);
    } else {
      //@ assert minVal == oldMin;
      //@ assert maxVal == oldMax;
      //@ assert oldMin <= a[i];
      //@ assert a[i] <= oldMax;
      //@ assert Min_logic(a, i + 1) == (a[i] <= Min_logic(a, i) ? a[i] : Min_logic(a, i));
      //@ assert Min_logic(a, i + 1) == Min_logic(a, i);
      //@ assert minVal == Min_logic(a, i + 1);
      //@ assert Max_logic(a, i + 1) == (a[i] >= Max_logic(a, i) ? a[i] : Max_logic(a, i));
      //@ assert Max_logic(a, i + 1) == Max_logic(a, i);
      //@ assert maxVal == Max_logic(a, i + 1);
    }

    //@ assert minVal == Min_logic(a, i + 1);
    //@ assert maxVal == Max_logic(a, i + 1);
    //@ assert Min_logic(a, i + 1) <= Max_logic(a, i + 1);
    //@ assert minVal <= maxVal;
    //@ assert \forall integer k; 0 <= k && k < i + 1 ==> Min_logic(a, i + 1) <= a[k];
    //@ assert \forall integer k; 0 <= k && k < i + 1 ==> a[k] <= Max_logic(a, i + 1);
    //@ assert \forall integer k; 0 <= k && k < i + 1 ==> minVal <= a[k] && a[k] <= maxVal;

    i++;

    //@ assert minVal == Min_logic(a, i);
    //@ assert maxVal == Max_logic(a, i);
    //@ assert \forall integer k; 0 <= k && k < i ==> minVal <= a[k] && a[k] <= maxVal;
  }

  //@ assert i == n;
  //@ assert minVal == Min_logic(a, n);
  //@ assert maxVal == Max_logic(a, n);
  //@ assert INT_MIN <= maxVal - minVal;
  //@ assert maxVal - minVal <= INT_MAX;
  return maxVal - minVal;
}