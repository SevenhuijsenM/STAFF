/*@ axiomatic EuclideanModulo {
      logic integer euclidean_mod(integer a, integer m);

      axiom euclidean_mod_range:
        \forall integer a, m;
          m > 0 ==> 0 <= euclidean_mod(a, m) && euclidean_mod(a, m) < m;

      axiom euclidean_mod_congruence:
        \forall integer a, m;
          m > 0 ==> \exists integer q; a == q * m + euclidean_mod(a, m);

      axiom euclidean_mod_unique:
        \forall integer a, m, r;
          m > 0 &&
          0 <= r &&
          r < m &&
          (\exists integer q; a == q * m + r)
          ==> euclidean_mod(a, m) == r;
    }
*/

#ifdef __FRAMAC__

/*@
  requires m > 0;
  assigns \nothing;
  ensures \result == euclidean_mod(a, m);
  ensures 0 <= \result;
  ensures \result < m;
*/
int dafny_mod_ll(long long a, int m);

#else

/*@
  requires m > 0;
  assigns \nothing;
  ensures \result == euclidean_mod(a, m);
  ensures 0 <= \result;
  ensures \result < m;
*/
static int dafny_mod_ll(long long a, int m)
{
    long long rem = a % (long long)m;

    if (rem < 0) {
        rem += (long long)m;
    }

    return (int)rem;
}

#endif

/*@
  requires len >= 0;
  requires n >= 0;
  requires len == 0 || \valid_read(l + (0 .. len - 1));
  requires len == 0 || \valid(r + (0 .. len - 1));
  requires len == 0 || \separated(l + (0 .. len - 1), r + (0 .. len - 1));
  assigns r[0 .. len - 1];
  ensures \result == len;
  ensures \forall integer j;
            0 <= j && j < len ==>
              r[j] == \old(l[euclidean_mod(j - n + len, len)]);
*/
int RotateRight(const int *l, int len, int n, int *r)
{
    int i = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= len;
      loop invariant \forall integer k;
        0 <= k && k < i ==>
          r[k] == \at(l[euclidean_mod(k - n + len, len)], Pre);
      loop assigns i, r[0 .. len - 1];
      loop variant len - i;
    */
    for (i = 0; i < len; i++) {
        long long a = (long long)i - (long long)n + (long long)len;
        //@ assert len > 0;
        //@ assert a == i - n + len;

        int idx = dafny_mod_ll(a, len);

        //@ assert idx == euclidean_mod(i - n + len, len);
        //@ assert 0 <= idx;
        //@ assert idx < len;

        r[i] = l[idx];

        //@ assert r[i] == \at(l[euclidean_mod(i - n + len, len)], Pre);
    }

    //@ assert i == len;
    return len;
}