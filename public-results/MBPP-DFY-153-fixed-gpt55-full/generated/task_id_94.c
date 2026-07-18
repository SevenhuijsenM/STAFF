/*@
  requires s_len > 0;
  requires \valid_read(s + (0 .. s_len - 1));
  requires \forall integer i; 0 <= i && i < s_len ==> \valid_read(s[i] + (0 .. 1));
  assigns \nothing;
  ensures \exists integer i;
            0 <= i && i < s_len &&
            \result == s[i][0] &&
            (\forall integer j; 0 <= j && j < s_len ==> s[i][1] <= s[j][1]);
*/
int MinSecondValueFirst(int **s, int s_len)
{
    int minSecondIndex = 0;

    /*@
      loop invariant 1 <= i && i <= s_len;
      loop invariant 0 <= minSecondIndex && minSecondIndex < i;
      loop invariant \forall integer j;
                        0 <= j && j < i ==> s[minSecondIndex][1] <= s[j][1];
      loop assigns i, minSecondIndex;
      loop variant s_len - i;
    */
    for (int i = 1; i < s_len; i++) {
        if (s[i][1] < s[minSecondIndex][1]) {
            minSecondIndex = i;
        }
    }

    return s[minSecondIndex][0];
}