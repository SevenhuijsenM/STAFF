/*@
  requires length >= 0;
  requires length == 0 || \valid(a + (0 .. length - 1));
  assigns a[0 .. length - 1];
  ensures \forall integer k; 0 <= k && k < length ==> a[k] == \old(a[length - 1 - k]);
*/
void Reverse(int *a, int length)
{
  int i = 0;
  int j = length - 1;

  /*@
    loop invariant length >= 0;
    loop invariant length == 0 || \valid(a + (0 .. length - 1));
    loop invariant 0 <= i;
    loop invariant -1 <= j;
    loop invariant i <= length;
    loop invariant j < length;
    loop invariant i <= j + 1;
    loop invariant j == length - 1 - i;
    loop invariant i == length - 1 - j;
    loop invariant \forall integer p; 0 <= p && p < i ==> a[p] == \at(a[length - 1 - p], Pre);
    loop invariant \forall integer p; j < p && p < length ==> a[p] == \at(a[length - 1 - p], Pre);
    loop invariant \forall integer p; i <= p && p <= j ==> a[p] == \at(a[p], Pre);
    loop assigns i, j, a[0 .. length - 1];
    loop variant j - i + 1;
  */
  while (i < j) {
    //@ assert 0 <= i;
    //@ assert i < j;
    //@ assert 0 <= j;
    //@ assert j < length;
    //@ assert i < length;
    //@ assert j == length - 1 - i;
    //@ assert i == length - 1 - j;
    //@ assert a[i] == \at(a[i], Pre);
    //@ assert a[j] == \at(a[j], Pre);

    int tmp = a[i];
    int tmp2 = a[j];

    //@ assert tmp == \at(a[i], Pre);
    //@ assert tmp2 == \at(a[j], Pre);

    a[i] = tmp2;
    a[j] = tmp;

    //@ assert a[i] == tmp2;
    //@ assert a[j] == tmp;
    //@ assert a[i] == \at(a[j], Pre);
    //@ assert a[j] == \at(a[i], Pre);
    //@ assert a[i] == \at(a[length - 1 - i], Pre);
    //@ assert a[j] == \at(a[length - 1 - j], Pre);
    //@ assert \forall integer p; 0 <= p && p < i ==> a[p] == \at(a[length - 1 - p], Pre);
    //@ assert \forall integer p; j < p && p < length ==> a[p] == \at(a[length - 1 - p], Pre);
    //@ assert \forall integer p; i + 1 <= p && p <= j - 1 ==> a[p] == \at(a[p], Pre);
    //@ assert \forall integer p; 0 <= p && p < i + 1 ==> a[p] == \at(a[length - 1 - p], Pre);
    //@ assert \forall integer p; j - 1 < p && p < length ==> a[p] == \at(a[length - 1 - p], Pre);
    //@ assert 0 <= i + 1;
    //@ assert -1 <= j - 1;
    //@ assert i + 1 <= (j - 1) + 1;
    //@ assert j - 1 == length - 1 - (i + 1);
    //@ assert i + 1 == length - 1 - (j - 1);

    i = i + 1;
    j = j - 1;
  }

  //@ assert i >= j;
  //@ assert i <= j + 1;
  //@ assert i == j || i == j + 1;
  //@ assert \forall integer k; 0 <= k && k < length && k < i ==> a[k] == \at(a[length - 1 - k], Pre);
  //@ assert \forall integer k; 0 <= k && k < length && j < k ==> a[k] == \at(a[length - 1 - k], Pre);
  //@ assert \forall integer k; 0 <= k && k < length && i <= k && k <= j ==> a[k] == \at(a[k], Pre);
  //@ assert \forall integer k; 0 <= k && k < length && i <= k && k <= j ==> i == j;
  //@ assert \forall integer k; 0 <= k && k < length && i <= k && k <= j ==> k == i;
  //@ assert \forall integer k; 0 <= k && k < length && i <= k && k <= j ==> k == j;
  //@ assert \forall integer k; 0 <= k && k < length && i <= k && k <= j ==> length - 1 - k == k;
  //@ assert \forall integer k; 0 <= k && k < length && i <= k && k <= j ==> a[k] == \at(a[length - 1 - k], Pre);
  //@ assert \forall integer k; 0 <= k && k < length ==> a[k] == \at(a[length - 1 - k], Pre);
}

/*@
  requires length >= 0;
  requires 2 <= k;
  requires k <= length;
  requires \valid(s + (0 .. length - 1));
  assigns s[0 .. k - 1];
  ensures \forall integer p; 0 <= p && p < k ==> s[p] == \old(s[k - 1 - p]);
  ensures \forall integer p; k <= p && p < length ==> s[p] == \old(s[p]);
*/
void ReverseUptoK(int *s, int k, int length)
{
  int i = 0;
  int j = k - 1;

  /*@
    loop invariant length >= 0;
    loop invariant 2 <= k;
    loop invariant k <= length;
    loop invariant \valid(s + (0 .. length - 1));
    loop invariant 0 <= i;
    loop invariant -1 <= j;
    loop invariant i <= k;
    loop invariant j < k;
    loop invariant i <= j + 1;
    loop invariant j == k - 1 - i;
    loop invariant i == k - 1 - j;
    loop invariant \forall integer p; 0 <= p && p < i ==> s[p] == \at(s[k - 1 - p], Pre);
    loop invariant \forall integer p; j < p && p < k ==> s[p] == \at(s[k - 1 - p], Pre);
    loop invariant \forall integer p; i <= p && p <= j ==> s[p] == \at(s[p], Pre);
    loop invariant \forall integer p; k <= p && p < length ==> s[p] == \at(s[p], Pre);
    loop assigns i, j, s[0 .. k - 1];
    loop variant j - i + 1;
  */
  while (i < j) {
    //@ assert 0 <= i;
    //@ assert i < j;
    //@ assert 0 <= j;
    //@ assert j < k;
    //@ assert i < k;
    //@ assert j == k - 1 - i;
    //@ assert i == k - 1 - j;
    //@ assert s[i] == \at(s[i], Pre);
    //@ assert s[j] == \at(s[j], Pre);

    int tmp = s[i];
    int tmp2 = s[j];

    //@ assert tmp == \at(s[i], Pre);
    //@ assert tmp2 == \at(s[j], Pre);

    s[i] = tmp2;
    s[j] = tmp;

    //@ assert s[i] == tmp2;
    //@ assert s[j] == tmp;
    //@ assert s[i] == \at(s[j], Pre);
    //@ assert s[j] == \at(s[i], Pre);
    //@ assert s[i] == \at(s[k - 1 - i], Pre);
    //@ assert s[j] == \at(s[k - 1 - j], Pre);
    //@ assert \forall integer p; 0 <= p && p < i ==> s[p] == \at(s[k - 1 - p], Pre);
    //@ assert \forall integer p; j < p && p < k ==> s[p] == \at(s[k - 1 - p], Pre);
    //@ assert \forall integer p; i + 1 <= p && p <= j - 1 ==> s[p] == \at(s[p], Pre);
    //@ assert \forall integer p; 0 <= p && p < i + 1 ==> s[p] == \at(s[k - 1 - p], Pre);
    //@ assert \forall integer p; j - 1 < p && p < k ==> s[p] == \at(s[k - 1 - p], Pre);
    //@ assert \forall integer p; k <= p && p < length ==> s[p] == \at(s[p], Pre);
    //@ assert 0 <= i + 1;
    //@ assert -1 <= j - 1;
    //@ assert i + 1 <= (j - 1) + 1;
    //@ assert j - 1 == k - 1 - (i + 1);
    //@ assert i + 1 == k - 1 - (j - 1);

    i = i + 1;
    j = j - 1;
  }

  //@ assert i >= j;
  //@ assert i <= j + 1;
  //@ assert i == j || i == j + 1;
  //@ assert \forall integer p; 0 <= p && p < k && p < i ==> s[p] == \at(s[k - 1 - p], Pre);
  //@ assert \forall integer p; 0 <= p && p < k && j < p ==> s[p] == \at(s[k - 1 - p], Pre);
  //@ assert \forall integer p; 0 <= p && p < k && i <= p && p <= j ==> s[p] == \at(s[p], Pre);
  //@ assert \forall integer p; 0 <= p && p < k && i <= p && p <= j ==> i == j;
  //@ assert \forall integer p; 0 <= p && p < k && i <= p && p <= j ==> p == i;
  //@ assert \forall integer p; 0 <= p && p < k && i <= p && p <= j ==> p == j;
  //@ assert \forall integer p; 0 <= p && p < k && i <= p && p <= j ==> k - 1 - p == p;
  //@ assert \forall integer p; 0 <= p && p < k && i <= p && p <= j ==> s[p] == \at(s[k - 1 - p], Pre);
  //@ assert \forall integer p; 0 <= p && p < k ==> s[p] == \at(s[k - 1 - p], Pre);
  //@ assert \forall integer p; k <= p && p < length ==> s[p] == \at(s[p], Pre);
}