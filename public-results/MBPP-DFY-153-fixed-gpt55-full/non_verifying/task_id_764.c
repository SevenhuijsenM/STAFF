/*@
  predicate IsDigitLogic(integer c) =
    48 <= c && c <= 57;
*/

/*@
  axiomatic CountDigitsLogic {
    logic integer count_digits{L}(char *s, integer n)
      reads s[0 .. n-1];

    axiom count_digits_empty{L}:
      \forall char *s, integer n;
        n <= 0 ==> count_digits{L}(s, n) == 0;

    axiom count_digits_succ_digit{L}:
      \forall char *s, integer n;
        0 <= n && IsDigitLogic(\at(s[n], L)) ==>
          count_digits{L}(s, n + 1) == count_digits{L}(s, n) + 1;

    axiom count_digits_succ_nondigit{L}:
      \forall char *s, integer n;
        0 <= n && !IsDigitLogic(\at(s[n], L)) ==>
          count_digits{L}(s, n + 1) == count_digits{L}(s, n);

    axiom count_digits_nonnegative{L}:
      \forall char *s, integer n;
        0 <= n ==> 0 <= count_digits{L}(s, n);

    axiom count_digits_upper_bound{L}:
      \forall char *s, integer n;
        0 <= n ==> count_digits{L}(s, n) <= n;
  }
*/

/*@
  assigns \nothing;
  ensures 0 <= \result;
  ensures \result <= 1;
  ensures (\result != 0) <==> IsDigitLogic(c);
*/
int IsDigit(char c)
{
    return c >= '0' && c <= '9';
}

/*@
  requires 0 <= len;
  requires len == 0 || \valid_read(s + (0 .. len - 1));
  assigns \nothing;
  ensures 0 <= \result;
  ensures \result <= len;
  ensures \result == count_digits{Pre}(s, len);
*/
int CountDigits(char *s, int len)
{
    int count = 0;
    int i = 0;
    int digit = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= len;
      loop invariant 0 <= count;
      loop invariant count <= i;
      loop invariant count == count_digits{Pre}(s, i);
      loop assigns i, count, digit;
      loop variant len - i;
    */
    while (i < len) {
        //@ assert 0 <= i;
        //@ assert i < len;
        //@ assert \valid_read(s + i);
        //@ assert s[i] == \at(s[i], Pre);

        digit = IsDigit(s[i]);

        //@ assert 0 <= digit;
        //@ assert digit <= 1;
        //@ assert (digit != 0) <==> IsDigitLogic(s[i]);
        //@ assert s[i] == \at(s[i], Pre);

        if (digit != 0) {
            //@ assert IsDigitLogic(s[i]);
            //@ assert IsDigitLogic(\at(s[i], Pre));
            //@ assert count_digits{Pre}(s, i + 1) == count_digits{Pre}(s, i) + 1;
            count++;
            //@ assert count == count_digits{Pre}(s, i + 1);
        } else {
            //@ assert !IsDigitLogic(s[i]);
            //@ assert !IsDigitLogic(\at(s[i], Pre));
            //@ assert count_digits{Pre}(s, i + 1) == count_digits{Pre}(s, i);
            //@ assert count == count_digits{Pre}(s, i + 1);
        }

        //@ assert count == count_digits{Pre}(s, i + 1);
        i++;
        //@ assert count == count_digits{Pre}(s, i);
    }

    //@ assert i == len;
    //@ assert count == count_digits{Pre}(s, len);
    return count;
}