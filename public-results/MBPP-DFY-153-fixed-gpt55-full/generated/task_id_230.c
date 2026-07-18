typedef struct {
  char *data;
  int length;
} String;

/*@
  requires s.length >= 0;
  requires s.data != \null;
  requires buffer != \null;
  requires s.length == 0 || \valid_read(s.data + (0 .. s.length - 1));
  requires s.length == 0 || \valid(buffer + (0 .. s.length - 1));
  requires s.length == 0 || \separated(s.data + (0 .. s.length - 1), buffer + (0 .. s.length - 1));
  assigns buffer[0 .. s.length - 1];
  ensures \result.length == s.length;
  ensures \result.data == buffer;
  ensures \forall integer i;
            0 <= i && i < s.length ==>
              ((s.data[i] == ' ' ==> \result.data[i] == ch) &&
               (s.data[i] != ' ' ==> \result.data[i] == s.data[i]));
*/
String ReplaceBlanksWithChar(String s, char ch, char *buffer)
{
  String result;
  result.data = buffer;
  result.length = s.length;

  int i = 0;

  /*@
    loop invariant 0 <= i && i <= s.length;
    loop invariant result.data == buffer;
    loop invariant result.length == s.length;
    loop invariant \forall integer k;
              0 <= k && k < i ==>
                ((s.data[k] == ' ' ==> buffer[k] == ch) &&
                 (s.data[k] != ' ' ==> buffer[k] == s.data[k]));
    loop assigns i, buffer[0 .. s.length - 1];
    loop variant s.length - i;
  */
  for (i = 0; i < s.length; i++) {
    if (s.data[i] == ' ') {
      buffer[i] = ch;
    } else {
      buffer[i] = s.data[i];
    }
  }

  return result;
}