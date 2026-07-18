#include <stddef.h>

typedef struct {
    char *data;
    size_t length;
} CharSeq;

/*@
  requires len == 0 || \valid_read(s + (0 .. len - 1));
  requires len == 0 || \valid(buffer + (0 .. len - 1));
  requires len == 0 || \separated(s + (0 .. len - 1), buffer + (0 .. len - 1));
  assigns buffer[0 .. len - 1];
  ensures \result.data == buffer;
  ensures \result.length == len;
  ensures \forall integer i; 0 <= i && i < len ==> \result.data[i] == s[i];
*/
CharSeq SplitStringIntoChars(const char *s, size_t len, char *buffer)
{
    CharSeq v;
    v.data = buffer;
    v.length = 0;

    size_t i = 0;

    /*@
      loop invariant 0 <= i && i <= len;
      loop invariant v.data == buffer;
      loop invariant v.length == i;
      loop invariant \forall integer k; 0 <= k && k < i ==> buffer[k] == s[k];
      loop assigns i, v.length, buffer[0 .. len - 1];
      loop variant len - i;
    */
    while (i < len) {
        buffer[i] = s[i];
        //@ assert buffer[i] == s[i];
        //@ assert \forall integer k; 0 <= k && k < i + 1 ==> buffer[k] == s[k];
        i++;
        v.length = i;
    }

    return v;
}