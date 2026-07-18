#include <stdbool.h>
#include <stddef.h>

/*@
  predicate IsDigitPred(char c) =
    48 <= (integer)c && (integer)c <= 57;
*/

/*@
  assigns \nothing;
  ensures (\result != 0) <==> IsDigitPred(c);
*/
bool IsDigit(char c)
{
    return ('0' <= c && c <= '9');
}

/*@
  requires n == 0 || \valid_read(s + (0 .. ((integer)n - 1)));
  assigns \nothing;
  ensures (\result != 0) <==>
    ((integer)n > 0 &&
     (\forall integer i; 0 <= i && i < (integer)n ==> IsDigitPred(s[i])));
*/
bool IsInteger(const char *s, size_t n)
{
    bool result = true;

    if (n == 0) {
        result = false;
    } else {
        size_t i = 0;

        /*@
          loop invariant 0 < (integer)n;
          loop invariant 0 <= (integer)i && (integer)i <= (integer)n;
          loop invariant (result != 0) <==>
            (\forall integer k; 0 <= k && k < (integer)i ==> IsDigitPred(s[k]));
          loop assigns i, result;
          loop variant (integer)n - (integer)i;
        */
        while (i < n) {
            if (!IsDigit(s[i])) {
                //@ assert !IsDigitPred(s[i]);
                result = false;
            } else {
                //@ assert IsDigitPred(s[i]);
            }
            i++;
        }
    }

    return result;
}

/*
  Conversion explanation:
  Dafny char/string values were represented as C char arrays with an explicit
  size_t length parameter n, because C pointers do not carry lengths. The
  precondition on IsInteger makes the readable range explicit and does not
  require null termination. The Dafny predicate IsDigit is represented both by
  the executable C function IsDigit and by the ACSL predicate IsDigitPred used
  in contracts. The Dafny postcondition of IsInteger is preserved as an ACSL
  ensures clause. The Dafny loop invariant relating result to the checked
  prefix of the string is translated directly, with bounds and a termination
  variant added in Frama-C-compatible ACSL form.
*/