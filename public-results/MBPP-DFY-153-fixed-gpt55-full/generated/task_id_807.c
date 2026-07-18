/*@ predicate is_odd(integer x) = x % 2 != 0; */

typedef struct {
  int found;
  int index;
} FindFirstOdd_result;

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result != 0 ==> is_odd(x);
  ensures is_odd(x) ==> \result != 0;
  ensures \result == 0 ==> !is_odd(x);
  ensures !is_odd(x) ==> \result == 0;
*/
int IsOdd(int x)
{
  if (x % 2 != 0) {
    return 1;
  }
  return 0;
}

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n-1));
  assigns \nothing;
  ensures \result.found == 0 || \result.found == 1;
  ensures \result.found == 0 ==> (\forall integer i; 0 <= i && i < n ==> !is_odd(a[i]));
  ensures \result.found != 0 ==> 0 <= \result.index && \result.index < n;
  ensures \result.found != 0 ==> is_odd(a[\result.index]);
  ensures \result.found != 0 ==> (\forall integer i; 0 <= i && i < \result.index ==> !is_odd(a[i]));
*/
FindFirstOdd_result FindFirstOdd(const int *a, int n)
{
  int index = 0;

  /*@
    loop invariant 0 <= index;
    loop invariant index <= n;
    loop invariant \forall integer i; 0 <= i && i < index ==> !is_odd(a[i]);
    loop assigns index;
    loop variant n - index;
  */
  while (index < n) {
    int odd;

    //@ assert 0 <= index;
    //@ assert index < n;
    odd = IsOdd(a[index]);

    if (odd) {
      FindFirstOdd_result r;

      //@ assert odd != 0;
      //@ assert is_odd(a[index]);
      //@ assert \forall integer i; 0 <= i && i < index ==> !is_odd(a[i]);

      r.found = 1;
      r.index = index;

      //@ assert r.found != 0;
      //@ assert 0 <= r.index;
      //@ assert r.index < n;
      //@ assert is_odd(a[r.index]);
      //@ assert \forall integer i; 0 <= i && i < r.index ==> !is_odd(a[i]);

      return r;
    }

    //@ assert odd == 0;
    //@ assert !is_odd(a[index]);
    //@ assert \forall integer i; 0 <= i && i < index ==> !is_odd(a[i]);
    //@ assert \forall integer i; 0 <= i && i < index + 1 ==> !is_odd(a[i]);

    index = index + 1;
  }

  //@ assert index == n;
  //@ assert \forall integer i; 0 <= i && i < n ==> !is_odd(a[i]);

  {
    FindFirstOdd_result r;
    r.found = 0;
    r.index = index;

    //@ assert r.found == 0;
    //@ assert r.found == 0 || r.found == 1;
    //@ assert \forall integer i; 0 <= i && i < n ==> !is_odd(a[i]);

    return r;
  }
}