#include <stddef.h>

typedef struct {
  char *data;
  size_t length;
} String;

/*@
  requires s.length == 0 || \valid_read(s.data + (0 .. s.length - 1));
  requires s.length == 0 || \valid(out_data + (0 .. s.length - 1));
  requires s.length == 0 || \separated(s.data + (0 .. s.length - 1), out_data + (0 .. s.length - 1));
  assigns out_data[0 .. s.length - 1];
  ensures \result.length == s.length;
  ensures \result.data == out_data;
  ensures \forall integer i; 0 <= i && i < s.length ==>
            ((s.data[i] == oldChar ==> \result.data[i] == newChar) &&
             (s.data[i] != oldChar ==> \result.data[i] == s.data[i]));
*/
String ReplaceChars(String s, char oldChar, char newChar, char *out_data) {
  String v;
  v.data = out_data;
  v.length = s.length;

  size_t i;

  /*@
    loop invariant 0 <= i && i <= s.length;
    loop invariant v.data == out_data;
    loop invariant v.length == s.length;
    loop invariant \forall integer k; 0 <= k && k < i ==>
              ((s.data[k] == oldChar ==> out_data[k] == newChar) &&
               (s.data[k] != oldChar ==> out_data[k] == s.data[k]));
    loop assigns i, out_data[0 .. s.length - 1];
    loop variant s.length - i;
  */
  for (i = 0; i < s.length; i++) {
    if (s.data[i] == oldChar) {
      out_data[i] = newChar;
    } else {
      out_data[i] = s.data[i];
    }
  }

  return v;
}