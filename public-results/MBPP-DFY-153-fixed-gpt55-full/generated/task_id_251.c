#include <limits.h>

/*@
  requires 0 <= s_len;
  requires s_len <= INT_MAX / 2;
  requires s_len == 0 || \valid_read(s + (0 .. s_len - 1));
  requires s_len == 0 || \valid(v + (0 .. 2 * s_len - 1));
  requires s_len == 0 || \separated(v + (0 .. 2 * s_len - 1), s + (0 .. s_len - 1));
  assigns v[0 .. 2 * s_len - 1];
  ensures \result == 2 * s_len;
  ensures \forall integer k; 0 <= k && k < s_len ==> v[2 * k] == x && v[2 * k + 1] == s[k];
*/
int InsertBeforeEach(const char * const *s, int s_len, const char *x, const char **v)
{
    int i = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= s_len;
      loop invariant \forall integer j; 0 <= j && j < i ==> v[2 * j] == x;
      loop invariant \forall integer j; 0 <= j && j < i ==> v[2 * j + 1] == s[j];
      loop assigns i, v[0 .. 2 * s_len - 1];
      loop variant s_len - i;
    */
    for (i = 0; i < s_len; i++) {
        //@ assert 0 <= i;
        //@ assert i < s_len;
        //@ assert 0 <= 2 * i;
        //@ assert 2 * i + 1 < 2 * s_len;
        //@ assert \forall integer j; 0 <= j && j < i ==> 2 * j != 2 * i;
        //@ assert \forall integer j; 0 <= j && j < i ==> 2 * j + 1 != 2 * i;
        v[2 * i] = x;
        //@ assert v[2 * i] == x;
        //@ assert \forall integer j; 0 <= j && j < i ==> v[2 * j] == x;
        //@ assert \forall integer j; 0 <= j && j < i ==> v[2 * j + 1] == s[j];
        //@ assert \forall integer j; 0 <= j && j < i ==> 2 * j != 2 * i + 1;
        //@ assert \forall integer j; 0 <= j && j < i ==> 2 * j + 1 != 2 * i + 1;
        //@ assert 2 * i != 2 * i + 1;
        v[2 * i + 1] = s[i];
        //@ assert v[2 * i] == x;
        //@ assert v[2 * i + 1] == s[i];
        //@ assert \forall integer j; 0 <= j && j < i ==> v[2 * j] == x;
        //@ assert \forall integer j; 0 <= j && j < i ==> v[2 * j + 1] == s[j];
        //@ assert \forall integer j; 0 <= j && j < i + 1 ==> (j < i || j == i);
        //@ assert \forall integer j; 0 <= j && j < i + 1 ==> v[2 * j] == x;
        //@ assert \forall integer j; 0 <= j && j < i + 1 ==> v[2 * j + 1] == s[j];
    }

    //@ assert i == s_len;
    //@ assert \forall integer k; 0 <= k && k < s_len ==> v[2 * k] == x;
    //@ assert \forall integer k; 0 <= k && k < s_len ==> v[2 * k + 1] == s[k];
    //@ assert \forall integer k; 0 <= k && k < s_len ==> v[2 * k] == x && v[2 * k + 1] == s[k];
    return 2 * s_len;
}