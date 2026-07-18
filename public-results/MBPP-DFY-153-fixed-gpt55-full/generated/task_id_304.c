/*@ logic integer dafny_mod(integer a, integer m) =
      (m <= 0 ? 0 : ((a % m) + m) % m);
*/

/*@
  requires m > 0;
  assigns \nothing;
  ensures \result == dafny_mod(a, m);
  ensures 0 <= \result && \result < m;
*/
static int DafnyEuclideanMod(long long a, int m)
{
    long long r = a % (long long)m;

    if (r < 0) {
        r += (long long)m;
    }

    return (int)r;
}

/*@
  requires len > 0;
  requires \valid_read(l + (0 .. len - 1));
  requires n >= 0;
  requires 0 <= index && index < len;
  assigns \nothing;
  ensures \result == l[dafny_mod(index - n + len, len)];
*/
int ElementAtIndexAfterRotation(const int *l, int len, int n, int index)
{
    long long rotated_index_expression =
        (long long)index - (long long)n + (long long)len;
    int rotated_index = DafnyEuclideanMod(rotated_index_expression, len);

    return l[rotated_index];
}