#include <stdbool.h>

/* Result type corresponding to Dafny returns (found: bool, c: char). */
typedef struct {
  bool found;
  char c;
} FindFirstRepeatedChar_result;

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(s + (0 .. n-1));
  assigns \nothing;

  ensures \result.found != 0 ==>
    (\exists integer i, j;
      0 <= i && i < j && j < n &&
      s[i] == s[j] &&
      s[i] == \result.c &&
      (\forall integer k, l;
        0 <= k && k < l && l < j && s[k] == s[l] ==> k >= i));

  ensures \result.found == 0 ==>
    (\forall integer i, j;
      0 <= i && i < j && j < n ==> s[i] != s[j]);
*/
FindFirstRepeatedChar_result FindFirstRepeatedChar(const char *s, int n) {
  FindFirstRepeatedChar_result res;
  res.c = ' ';
  res.found = false;

  bool inner_found = false;
  int i = 0;

  /*@
    loop invariant 0 <= i && i <= n;

    loop invariant (res.found != 0) <==> (inner_found != 0);

    loop invariant res.found != 0 ==>
      (\exists integer ii, jj;
        0 <= ii && ii < i &&
        ii < jj && jj < n &&
        s[ii] == s[jj] &&
        s[ii] == res.c &&
        (\forall integer k, l;
          0 <= k && k < l && l < jj && s[k] == s[l] ==> k >= ii));

    loop invariant res.found == 0 <==>
      (\forall integer ii, jj;
        0 <= ii && ii < i && ii < jj && jj < n ==> s[ii] != s[jj]);

    loop assigns i, inner_found, res.found, res.c;
    loop variant n - i;
  */
  while (i < n && !res.found) {
    int j = i + 1;

    /*@
      loop invariant 0 <= i && i < n;
      loop invariant i < j && j <= n;
      loop invariant res.found == 0;

      loop invariant inner_found != 0 ==>
        (\exists integer k;
          i < k && k < n &&
          s[i] == s[k] &&
          s[i] == res.c);

      loop invariant inner_found == 0 <==>
        (\forall integer k;
          i < k && k < j ==> s[i] != s[k]);

      loop assigns j, inner_found, res.c;
      loop variant n - j;
    */
    while (j < n && !inner_found) {
      if (s[i] == s[j]) {
        inner_found = true;
        res.c = s[i];
      }
      j = j + 1;
    }

    res.found = inner_found;
    i = i + 1;
  }

  return res;
}