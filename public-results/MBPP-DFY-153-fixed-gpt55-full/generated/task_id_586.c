/*@
  axiomatic ModuloAxioms {
    axiom mod_small:
      \forall integer a, m; m > 0 && 0 <= a && a < m ==> a % m == a;

    axiom mod_plus:
      \forall integer a, m; m > 0 && 0 <= a && a < m ==> (m + a) % m == a;
  }
*/

/*@
  requires len > 0;
  requires n >= 0;
  requires n < len;
  requires \valid_read(l + (0 .. len - 1));
  requires \valid(r + (0 .. len - 1));
  requires \separated(l + (0 .. len - 1), r + (0 .. len - 1));
  assigns r[0 .. len - 1];
  ensures \forall integer i; 0 <= i && i < len ==> r[i] == l[(i + n) % len];
*/
void SplitAndAppend(const int *l, int len, int n, int *r)
{
    int i;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= len - n;
      loop invariant \forall integer k; 0 <= k && k < i ==> r[k] == l[(k + n) % len];
      loop assigns i, r[0 .. len - 1];
      loop variant len - n - i;
    */
    for (i = 0; i < len - n; i++) {
        //@ assert 0 <= i;
        //@ assert i < len - n;
        //@ assert 0 <= i + n;
        //@ assert i + n < len;
        //@ assert (i + n) % len == i + n;
        r[i] = l[n + i];
        //@ assert r[i] == l[(i + n) % len];
    }

    //@ assert i == len - n;
    //@ assert \forall integer k; 0 <= k && k < len - n ==> r[k] == l[(k + n) % len];

    int j;

    /*@
      loop invariant 0 <= j;
      loop invariant j <= n;
      loop invariant \forall integer k; 0 <= k && k < len - n ==> r[k] == l[(k + n) % len];
      loop invariant \forall integer k; len - n <= k && k < len - n + j ==> r[k] == l[(k + n) % len];
      loop assigns j, r[0 .. len - 1];
      loop variant n - j;
    */
    for (j = 0; j < n; j++) {
        //@ assert 0 <= j;
        //@ assert j < n;
        //@ assert j < len;
        //@ assert len - n <= len - n + j;
        //@ assert len - n + j < len;
        //@ assert (len + j) % len == j;
        //@ assert len - n + j + n == len + j;
        //@ assert (len - n + j + n) % len == j;
        r[len - n + j] = l[j];
        //@ assert r[len - n + j] == l[((len - n + j) + n) % len];
    }

    //@ assert j == n;
    //@ assert len - n + j == len;
    //@ assert \forall integer k; 0 <= k && k < len - n ==> r[k] == l[(k + n) % len];
    //@ assert \forall integer k; len - n <= k && k < len ==> r[k] == l[(k + n) % len];

    int t;

    /*@
      loop invariant 0 <= t;
      loop invariant t <= len;
      loop invariant \forall integer k; 0 <= k && k < len - n ==> r[k] == l[(k + n) % len];
      loop invariant \forall integer k; len - n <= k && k < len ==> r[k] == l[(k + n) % len];
      loop invariant \forall integer k; 0 <= k && k < t ==> r[k] == l[(k + n) % len];
      loop assigns t;
      loop variant len - t;
    */
    for (t = 0; t < len; t++) {
        if (t < len - n) {
            //@ assert 0 <= t;
            //@ assert t < len - n;
            //@ assert r[t] == l[(t + n) % len];
        } else {
            //@ assert len - n <= t;
            //@ assert t < len;
            //@ assert r[t] == l[(t + n) % len];
        }
    }

    //@ assert t == len;
    //@ assert \forall integer k; 0 <= k && k < len ==> r[k] == l[(k + n) % len];
}