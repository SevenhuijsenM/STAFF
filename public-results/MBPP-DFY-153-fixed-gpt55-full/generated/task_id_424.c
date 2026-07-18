/*@
  requires 0 <= l_len;

  requires l_len == 0 || \valid_read(l + (0 .. l_len - 1));
  requires l_len == 0 || \valid_read(str_lens + (0 .. l_len - 1));
  requires l_len == 0 || \valid(r + (0 .. l_len - 1));
  requires \valid(r_len);

  requires \forall integer i; 0 <= i && i < l_len ==> str_lens[i] > 0;
  requires \forall integer i; 0 <= i && i < l_len ==> \valid_read(l[i] + (0 .. str_lens[i] - 1));

  requires l_len == 0 || \separated(r + (0 .. l_len - 1), r_len);
  requires l_len == 0 || \separated(r + (0 .. l_len - 1), l + (0 .. l_len - 1));
  requires l_len == 0 || \separated(r + (0 .. l_len - 1), str_lens + (0 .. l_len - 1));
  requires l_len == 0 || \separated(r_len, l + (0 .. l_len - 1));
  requires l_len == 0 || \separated(r_len, str_lens + (0 .. l_len - 1));
  requires \forall integer i; 0 <= i && i < l_len ==> \separated(r + (0 .. l_len - 1), l[i] + (0 .. str_lens[i] - 1));
  requires \forall integer i; 0 <= i && i < l_len ==> \separated(r_len, l[i] + (0 .. str_lens[i] - 1));

  assigns r[0 .. l_len - 1], *r_len;

  ensures *r_len == l_len;
  ensures \forall integer i; 0 <= i && i < l_len ==> r[i] == l[i][str_lens[i] - 1];
*/
void ExtractRearChars(const char * const l[], const int str_lens[], int l_len, char r[], int *r_len)
{
    int i;

    *r_len = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= l_len;
      loop invariant *r_len == i;
      loop invariant \forall integer k; 0 <= k && k < i ==> r[k] == l[k][str_lens[k] - 1];
      loop assigns i, r[0 .. l_len - 1], *r_len;
      loop variant l_len - i;
    */
    for (i = 0; i < l_len; i++) {
        //@ assert 0 <= i;
        //@ assert i < l_len;
        //@ assert i + 1 <= l_len;
        //@ assert l_len > 0;
        //@ assert str_lens[i] > 0;
        //@ assert \valid(r + i);
        //@ assert \valid_read(l[i] + (0 .. str_lens[i] - 1));
        //@ assert \valid_read(l[i] + (str_lens[i] - 1));
        //@ assert \separated(r + (0 .. l_len - 1), r_len);
        //@ assert \separated(r + (0 .. l_len - 1), l + (0 .. l_len - 1));
        //@ assert \separated(r + (0 .. l_len - 1), str_lens + (0 .. l_len - 1));
        //@ assert \separated(r_len, l + (0 .. l_len - 1));
        //@ assert \separated(r_len, str_lens + (0 .. l_len - 1));
        //@ assert \separated(r + (0 .. l_len - 1), l[i] + (0 .. str_lens[i] - 1));
        //@ assert \separated(r_len, l[i] + (0 .. str_lens[i] - 1));

        r[i] = l[i][str_lens[i] - 1];

        //@ assert r[i] == l[i][str_lens[i] - 1];
        //@ assert \forall integer k; 0 <= k && k < i ==> r[k] == l[k][str_lens[k] - 1];
        //@ assert \forall integer k; 0 <= k && k < i + 1 ==> (k < i || k == i);
        //@ assert \forall integer k; 0 <= k && k < i + 1 ==> r[k] == l[k][str_lens[k] - 1];

        *r_len = i + 1;

        //@ assert *r_len == i + 1;
        //@ assert \forall integer k; 0 <= k && k < i + 1 ==> r[k] == l[k][str_lens[k] - 1];
    }

    //@ assert i == l_len;
    //@ assert *r_len == l_len;
    //@ assert \forall integer k; 0 <= k && k < l_len ==> r[k] == l[k][str_lens[k] - 1];
}