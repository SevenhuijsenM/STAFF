typedef struct {
  int *data;
  int length;
} IntArray;

/*@
  requires n >= 1;
  requires 0 <= k && k < n;
  requires \valid_read(s + (0 .. n - 1));
  requires \valid(out);
  requires n == 1 || \valid(out + (0 .. n - 2));
  requires n == 1 || \separated(s + (0 .. n - 1), out + (0 .. n - 2));
  assigns out[0 .. n - 2];
  ensures \result.length == n - 1;
  ensures \result.data == out;
  ensures \result.length == 0 || \valid(\result.data + (0 .. \result.length - 1));
  ensures \forall integer i; 0 <= i && i < k ==> \result.data[i] == s[i];
  ensures \forall integer i; k <= i && i < \result.length ==> \result.data[i] == s[i + 1];
*/
IntArray RemoveElement(const int *s, int n, int k, int *out) {
  IntArray v;
  v.data = out;
  v.length = n - 1;

  int i = 0;

  /*@
    loop invariant 0 <= i && i <= k;
    loop invariant v.data == out;
    loop invariant v.length == n - 1;
    loop invariant \forall integer j; 0 <= j && j < i ==> v.data[j] == s[j];
    loop assigns i, out[0 .. k - 1];
    loop variant k - i;
  */
  while (i < k) {
    v.data[i] = s[i];
    i = i + 1;
  }

  //@ assert \forall integer j; 0 <= j && j < k ==> v.data[j] == s[j];

  /*@
    loop invariant k <= i && i <= v.length;
    loop invariant v.data == out;
    loop invariant v.length == n - 1;
    loop invariant \forall integer j; 0 <= j && j < k ==> v.data[j] == s[j];
    loop invariant \forall integer j; k <= j && j < i ==> v.data[j] == s[j + 1];
    loop assigns i, out[k .. n - 2];
    loop variant v.length - i;
  */
  while (i < v.length) {
    v.data[i] = s[i + 1];
    i = i + 1;
  }

  return v;
}