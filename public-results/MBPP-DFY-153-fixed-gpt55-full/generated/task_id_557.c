#include <stddef.h>

/*@ predicate IsLowerCase_pred(integer c) =
      97 <= c && c <= 122;
*/

/*@ predicate IsUpperCase_pred(integer c) =
      65 <= c && c <= 90;
*/

/*@ predicate IsLowerUpperPair_pred(integer c, integer C) =
      c == C + 32;
*/

/*@ predicate IsUpperLowerPair_pred(integer C, integer c) =
      C == c - 32;
*/

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> IsLowerCase_pred(c);
*/
int IsLowerCase(unsigned char c)
{
    return 97 <= c && c <= 122;
}

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> IsUpperCase_pred(c);
*/
int IsUpperCase(unsigned char c)
{
    return 65 <= c && c <= 90;
}

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> IsLowerUpperPair_pred(c, C);
*/
int IsLowerUpperPair(unsigned char c, unsigned char C)
{
    return (int)c == (int)C + 32;
}

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> IsUpperLowerPair_pred(C, c);
*/
int IsUpperLowerPair(unsigned char C, unsigned char c)
{
    return (int)C == (int)c - 32;
}

/*@
  assigns \nothing;
  ensures 0 <= \result && \result < 128;
  ensures \exists integer q; (integer)\result == (integer)c - 32 - 128 * q;
  ensures IsLowerCase_pred(c) ==> IsLowerUpperPair_pred(c, \result);
*/
unsigned char ShiftMinus32(unsigned char c)
{
    int r = ((int)c - 32) % 128;
    if (r < 0) {
        r += 128;
    }
    return (unsigned char)r;
}

/*@
  assigns \nothing;
  ensures 0 <= \result && \result < 128;
  ensures \exists integer q; (integer)\result == (integer)c + 32 - 128 * q;
  ensures IsUpperCase_pred(c) ==> IsUpperLowerPair_pred(c, \result);
*/
unsigned char Shift32(unsigned char c)
{
    int r = ((int)c + 32) % 128;
    return (unsigned char)r;
}

/*@
  requires n == 0 || \valid_read(s + (0 .. n - 1));
  requires n == 0 || \valid(v + (0 .. n - 1));
  requires n == 0 || \separated(s + (0 .. n - 1), v + (0 .. n - 1));
  assigns v[0 .. n - 1];
  ensures \result == n;
  ensures \forall integer i; 0 <= i && i < (integer)n && IsLowerCase_pred(s[i]) ==> IsLowerUpperPair_pred(s[i], v[i]);
  ensures \forall integer i; 0 <= i && i < (integer)n && IsUpperCase_pred(s[i]) ==> IsUpperLowerPair_pred(s[i], v[i]);
  ensures \forall integer i; 0 <= i && i < (integer)n && !IsLowerCase_pred(s[i]) && !IsUpperCase_pred(s[i]) ==> v[i] == s[i];
*/
size_t ToggleCase(const unsigned char *s, size_t n, unsigned char *v)
{
    size_t i = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant \forall integer k; 0 <= k && k < (integer)i && IsLowerCase_pred(s[k]) ==> IsLowerUpperPair_pred(s[k], v[k]);
      loop invariant \forall integer k; 0 <= k && k < (integer)i && IsUpperCase_pred(s[k]) ==> IsUpperLowerPair_pred(s[k], v[k]);
      loop invariant \forall integer k; 0 <= k && k < (integer)i && !IsLowerCase_pred(s[k]) && !IsUpperCase_pred(s[k]) ==> v[k] == s[k];
      loop assigns i, v[0 .. n - 1];
      loop variant (integer)n - (integer)i;
    */
    while (i < n) {
        if (IsLowerCase(s[i])) {
            v[i] = ShiftMinus32(s[i]);
        } else if (IsUpperCase(s[i])) {
            v[i] = Shift32(s[i]);
        } else {
            v[i] = s[i];
        }
        i++;
    }

    return n;
}