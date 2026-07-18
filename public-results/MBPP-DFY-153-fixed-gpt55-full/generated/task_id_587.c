/*@
  requires a_len >= 0;
  requires a_len == 0 || \valid_read(a + (0 .. a_len-1));
  requires a_len == 0 || \valid(s + (0 .. a_len-1));
  requires a_len == 0 || \separated(a + (0 .. a_len-1), s + (0 .. a_len-1));
  assigns s[0 .. a_len-1];
  ensures \result == a_len;
  ensures \forall integer i; 0 <= i && i < a_len ==> s[i] == a[i];
*/
int ArrayToSeq(const int *a, int a_len, int *s)
{
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= a_len;
      loop invariant \forall integer j; 0 <= j && j < i ==> s[j] == a[j];
      loop assigns i, s[0 .. a_len-1];
      loop variant a_len - i;
    */
    for (i = 0; i < a_len; i++) {
        s[i] = a[i];
    }

    return a_len;
}