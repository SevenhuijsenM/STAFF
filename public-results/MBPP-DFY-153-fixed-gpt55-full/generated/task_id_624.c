#include <stddef.h>
#include <stdbool.h>

/*@
  assigns \nothing;
  ensures (\result != 0) <==> (97 <= c && c <= 122);
*/
bool IsLowerCase(unsigned char c)
{
    return (97 <= c && c <= 122);
}

/*@
  assigns \nothing;
  ensures (\result != 0) <==> ((int)c == (int)C + 32);
*/
bool IsLowerUpperPair(unsigned char c, unsigned char C)
{
    return ((int)c == (int)C + 32);
}

/*@
  assigns \nothing;
  ensures 0 <= \result && \result < 128;
  ensures \result == (c + 96) % 128;
  ensures (97 <= c && c <= 122) ==> c == \result + 32;
*/
unsigned char ShiftMinus32(unsigned char c)
{
    int r = ((int)c + 96) % 128;
    return (unsigned char)r;
}

/*@
  requires n == 0 || \valid_read(s + (0 .. n-1));
  requires n == 0 || \valid(v + (0 .. n-1));
  requires n == 0 || \separated(s + (0 .. n-1), v + (0 .. n-1));
  assigns v[0 .. n-1];

  ensures \forall integer i;
    0 <= i && i < n && 97 <= \at(s[i], Pre) && \at(s[i], Pre) <= 122
    ==> \at(s[i], Pre) == v[i] + 32;

  ensures \forall integer i;
    0 <= i && i < n && !(97 <= \at(s[i], Pre) && \at(s[i], Pre) <= 122)
    ==> v[i] == \at(s[i], Pre);
*/
void ToUppercase(const unsigned char *s, size_t n, unsigned char *v)
{
    size_t i = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= n;

      loop invariant \forall integer k;
        0 <= k && k < i && 97 <= s[k] && s[k] <= 122
        ==> s[k] == v[k] + 32;

      loop invariant \forall integer k;
        0 <= k && k < i && !(97 <= s[k] && s[k] <= 122)
        ==> v[k] == s[k];

      loop assigns i, v[0 .. n-1];
      loop variant n - i;
    */
    for (; i < n; i++) {
        if (IsLowerCase(s[i])) {
            v[i] = ShiftMinus32(s[i]);
        } else {
            v[i] = s[i];
        }
    }
}