#include <limits.h>

/*@
axiomatic Factorial_Model {
  logic integer factorial_model(integer n);

  axiom factorial_zero:
    factorial_model(0) == 1;

  axiom factorial_step:
    \forall integer k;
      k > 0 ==> factorial_model(k) == k * factorial_model(k - 1);

  axiom factorial_nonnegative:
    \forall integer k;
      k >= 0 ==> 0 <= factorial_model(k);

  axiom factorial_previous_nonnegative:
    \forall integer k;
      k > 0 ==> 0 <= factorial_model(k - 1);

  axiom factorial_previous_le:
    \forall integer k;
      k > 0 ==> factorial_model(k - 1) <= factorial_model(k);

  axiom factorial_previous_fits_int:
    \forall integer k;
      k > 0 && factorial_model(k) <= INT_MAX ==> factorial_model(k - 1) <= INT_MAX;

  axiom factorial_digit_fits_int:
    \forall integer k;
      0 <= k && k <= 9 ==> factorial_model(k) <= INT_MAX;
}
*/

/*@
  requires 0 <= n;
  requires factorial_model(n) <= INT_MAX;
  assigns \nothing;
  decreases n;
  ensures \result == factorial_model(n);
  ensures 0 <= \result;
*/
int Factorial(int n)
{
  if (n == 0) {
    //@ assert factorial_model(0) == 1;
    return 1;
  }

  //@ assert 1 <= n;
  //@ assert 0 <= n - 1;
  //@ assert n - 1 < n;
  //@ assert factorial_model(n - 1) <= factorial_model(n);
  //@ assert factorial_model(n - 1) <= INT_MAX;
  int sub = Factorial(n - 1);

  //@ assert sub == factorial_model(n - 1);
  //@ assert 0 <= sub;
  //@ assert factorial_model(n) == n * factorial_model(n - 1);
  //@ assert n * sub == factorial_model(n);
  //@ assert 0 <= n * sub;
  //@ assert n * sub <= INT_MAX;
  //@ assert INT_MIN <= n * sub;
  return n * sub;
}

/*@
  requires 0 <= n;
  assigns \nothing;
  ensures \result == factorial_model(n % 10);
  ensures 0 <= \result;
*/
int FactorialOfLastDigit(int n)
{
  int lastDigit = n % 10;

  //@ assert lastDigit == n % 10;
  //@ assert 0 <= lastDigit;
  //@ assert lastDigit <= 9;
  //@ assert factorial_model(lastDigit) <= INT_MAX;
  int fact = Factorial(lastDigit);

  //@ assert fact == factorial_model(lastDigit);
  //@ assert lastDigit == n % 10;
  //@ assert fact == factorial_model(n % 10);
  return fact;
}