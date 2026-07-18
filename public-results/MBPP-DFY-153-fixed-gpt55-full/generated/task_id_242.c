typedef struct {
  const char *data;
  int length;
} DafnyString;

/*@
  requires s.length >= 0;
  requires s.length == 0 || \valid_read(s.data + (0 .. s.length - 1));
  assigns \nothing;
  ensures \result >= 0;
  ensures \result == s.length;
*/
int CountCharacters(DafnyString s) {
  int count = s.length;
  return count;
}