#include <stddef.h>

/*@
  predicate is_space_comma_dot_char(char c) =
    c == ' ' || c == ',' || c == '.';
*/

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result == 1) <==> is_space_comma_dot_char(c);
*/
int IsSpaceCommaDot(char c)
{
    return (c == ' ' || c == ',' || c == '.');
}

/*@
  requires n == 0 || \valid_read(s + (0 .. n - 1));
  requires n == 0 || \valid(v + (0 .. n - 1));
  requires n == 0 || \separated(s + (0 .. n - 1), v + (0 .. n - 1));
  assigns v[0 .. n - 1];
  ensures \result == v;
  ensures \forall integer i;
            0 <= i && i < n ==>
              ((is_space_comma_dot_char(s[i]) ==> v[i] == ':') &&
               (!is_space_comma_dot_char(s[i]) ==> v[i] == s[i]));
*/
char *ReplaceWithColon(const char *s, size_t n, char *v)
{
    size_t i = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant \forall integer k;
        0 <= k && k < i ==>
          ((is_space_comma_dot_char(s[k]) ==> v[k] == ':') &&
           (!is_space_comma_dot_char(s[k]) ==> v[k] == s[k]));
      loop assigns i, v[0 .. n - 1];
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        if (IsSpaceCommaDot(s[i])) {
            v[i] = ':';
        } else {
            v[i] = s[i];
        }
    }

    return v;
}