/*@
  predicate IsUpperCaseLogic(integer c) =
    65 <= c && c <= 90;

  axiomatic CountUppercaseModel {
    logic integer CountUppercaseRange{L}(unsigned char *s, integer n)
      reads s[0 .. n - 1];

    axiom CountUppercaseRange_empty{L}:
      \forall unsigned char *s;
        CountUppercaseRange{L}(s, 0) == 0;

    axiom CountUppercaseRange_step{L}:
      \forall unsigned char *s, integer n;
        n >= 0 && \valid_read{L}(s + (0 .. n)) ==>
          CountUppercaseRange{L}(s, n + 1) ==
            CountUppercaseRange{L}(s, n) +
            (IsUpperCaseLogic(\at(s[n], L)) ? 1 : 0);

    axiom CountUppercaseRange_nonnegative{L}:
      \forall unsigned char *s, integer n;
        n >= 0 ==> CountUppercaseRange{L}(s, n) >= 0;

    axiom CountUppercaseRange_upper_bound{L}:
      \forall unsigned char *s, integer n;
        n >= 0 ==> CountUppercaseRange{L}(s, n) <= n;
  }
*/

/*@
  assigns \nothing;
  ensures 0 <= \result;
  ensures \result <= 1;
  ensures \result == (IsUpperCaseLogic(c) ? 1 : 0);
  ensures (\result == 1) <==> IsUpperCaseLogic(c);
*/
int IsUpperCase(unsigned char c)
{
    if (c >= 65 && c <= 90) {
        //@ assert 65 <= c;
        //@ assert c <= 90;
        //@ assert IsUpperCaseLogic(c);
        return 1;
    }
    //@ assert c < 65 || c > 90;
    //@ assert !IsUpperCaseLogic(c);
    return 0;
}

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(s + (0 .. n - 1));
  assigns \nothing;
  ensures \result >= 0;
  ensures \result <= n;
  ensures \result == CountUppercaseRange{Here}(s, n);
*/
int CountUppercase(unsigned char *s, int n)
{
    int count = 0;
    int i = 0;

    //@ assert CountUppercaseRange{Here}(s, 0) == 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= n;
      loop invariant 0 <= count;
      loop invariant count <= i;
      loop invariant count == CountUppercaseRange{Here}(s, i);
      loop invariant n == 0 || \valid_read(s + (0 .. n - 1));
      loop assigns i, count;
      loop variant n - i;
    */
    while (i < n) {
        //@ assert 0 <= i;
        //@ assert i < n;
        //@ assert i + 1 <= n;
        //@ assert n > 0;
        //@ assert \valid_read(s + (0 .. n - 1));
        //@ assert \valid_read(s + i);
        //@ assert \valid_read(s + (0 .. i));

        int upper = IsUpperCase(s[i]);

        //@ assert upper == (IsUpperCaseLogic(s[i]) ? 1 : 0);
        //@ assert 0 <= upper;
        //@ assert upper <= 1;
        //@ assert CountUppercaseRange{Here}(s, i + 1) == CountUppercaseRange{Here}(s, i) + (IsUpperCaseLogic(s[i]) ? 1 : 0);
        //@ assert CountUppercaseRange{Here}(s, i + 1) == CountUppercaseRange{Here}(s, i) + upper;
        //@ assert count + upper >= 0;
        //@ assert count + upper <= i + 1;
        //@ assert count + upper <= n;

        count = count + upper;

        //@ assert count == CountUppercaseRange{Here}(s, i + 1);
        //@ assert 0 <= count;
        //@ assert count <= i + 1;

        i++;

        //@ assert count == CountUppercaseRange{Here}(s, i);
        //@ assert 0 <= i;
        //@ assert i <= n;
    }

    //@ assert i == n;
    //@ assert count == CountUppercaseRange{Here}(s, n);
    //@ assert 0 <= count;
    //@ assert count <= n;

    return count;
}