/*@ predicate IsUpperCaseChar(integer c) = 65 <= c && c <= 90; */

/*@ predicate IsUpperLowerPairChar(integer C, integer c) = C == c - 32; */

/*@ logic integer Shift32Char(integer c) = (c + 32) % 128; */

/*@
  assigns \nothing;
  ensures IsUpperCaseChar(c) ==> \result == 1;
  ensures !IsUpperCaseChar(c) ==> \result == 0;
*/
int IsUpperCase(unsigned char c)
{
    return 65 <= c && c <= 90;
}

/*@
  assigns \nothing;
  ensures IsUpperLowerPairChar(C, c) ==> \result == 1;
  ensures !IsUpperLowerPairChar(C, c) ==> \result == 0;
*/
int IsUpperLowerPair(unsigned char C, unsigned char c)
{
    return (int)C == (int)c - 32;
}

/*@
  assigns \nothing;
  ensures \result == Shift32Char(c);
  ensures 0 <= \result && \result < 128;
  ensures IsUpperCaseChar(c) ==> IsUpperLowerPairChar(c, \result);
*/
unsigned char Shift32(unsigned char c)
{
    return (unsigned char)(((int)c + 32) % 128);
}

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(s + (0 .. n-1));
  requires n == 0 || \valid(v + (0 .. n-1));
  requires n == 0 || \separated(s + (0 .. n-1), v + (0 .. n-1));
  assigns v[0 .. n-1];
  ensures \result == v;
  ensures \forall integer i; 0 <= i && i < n ==> (IsUpperCaseChar(s[i]) ==> IsUpperLowerPairChar(s[i], v[i]));
  ensures \forall integer i; 0 <= i && i < n ==> (!IsUpperCaseChar(s[i]) ==> v[i] == s[i]);
*/
unsigned char *ToLowercase(const unsigned char *s, int n, unsigned char *v)
{
    int i;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> (IsUpperCaseChar(s[k]) ==> IsUpperLowerPairChar(s[k], v[k]));
      loop invariant \forall integer k; 0 <= k && k < i ==> (!IsUpperCaseChar(s[k]) ==> v[k] == s[k]);
      loop assigns i, v[0 .. n-1];
      loop variant n - i;
    */
    for (i = 0; i < n; i++)
    {
        if (IsUpperCase(s[i]) != 0)
        {
            v[i] = Shift32(s[i]);
        }
        else
        {
            v[i] = s[i];
        }
    }

    return v;
}