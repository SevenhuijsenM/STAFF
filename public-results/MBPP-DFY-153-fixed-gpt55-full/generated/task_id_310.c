typedef struct {
  char *data;
  int length;
} CharArray;

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(s + (0 .. n - 1));
  requires n == 0 || \valid(buffer + (0 .. n - 1));
  requires n == 0 || \separated(s + (0 .. n - 1), buffer + (0 .. n - 1));
  assigns buffer[0 .. n - 1];
  ensures \result.length == n;
  ensures \result.data == buffer;
  ensures \forall integer i; 0 <= i && i < n ==> \result.data[i] == s[i];
*/
CharArray ToCharArray(const char *s, int n, char *buffer) {
  CharArray a;
  int i;

  a.data = buffer;
  a.length = n;

  /*@
    loop invariant 0 <= i && i <= n;
    loop invariant a.length == n;
    loop invariant a.data == buffer;
    loop invariant \forall integer k; 0 <= k && k < i ==> a.data[k] == s[k];
    loop assigns i, buffer[0 .. n - 1];
    loop variant n - i;
  */
  for (i = 0; i < n; i++) {
    a.data[i] = s[i];
  }

  return a;
}

/*
Conversion explanation:
The Dafny method ToCharArray takes an immutable string s and returns a newly
created array<char> a whose length is |s| and whose elements equal the
corresponding characters of s.

In C, a pointer alone does not carry length information, so the returned Dafny
array is represented by the CharArray structure, containing a data pointer and
an explicit length field. The Dafny string is represented as a read-only C
character buffer s with explicit length n. The caller supplies buffer as the
storage for the returned character array.

The Dafny postconditions are preserved as ACSL ensures clauses:
- a.Length == |s| is modeled by \result.length == n.
- forall i :: 0 <= i < |s| ==> a[i] == s[i] is modeled by the quantified ACSL
  postcondition over \result.data.

The Dafny loop invariants are translated directly:
- 0 <= i <= |s| becomes 0 <= i && i <= n.
- a.Length == |s| becomes a.length == n.
- the copied-prefix property is preserved with a universal quantifier.

The loop variant n - i is added to express termination in ACSL.
*/