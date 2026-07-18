#include <limits.h>
#include <stddef.h>

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  requires n == 0 || \valid_read(b + (0 .. n - 1));
  assigns \result;
  allocates \result;
  ensures \result != \null;
  ensures n == 0 || \valid(\result + (0 .. n - 1));
  ensures \fresh(\result, (integer)n * sizeof(int));
  ensures n == 0 || \separated(\result + (0 .. n - 1), a + (0 .. n - 1));
  ensures n == 0 || \separated(\result + (0 .. n - 1), b + (0 .. n - 1));
*/
int *alloc_int_array(int n, const int *a, const int *b);

/*@
  requires length >= 0;
  requires length == 0 || \valid_read(a + (0 .. length - 1));
  requires length == 0 || \valid_read(b + (0 .. length - 1));
  requires \forall integer i; 0 <= i && i < length ==> b[i] != 0;
  requires \forall integer i; 0 <= i && i < length ==> !(a[i] == INT_MIN && b[i] == -1);
  assigns \result, \result[0 .. length - 1];
  allocates \result;
  ensures \result != \null;
  ensures length == 0 || \valid(\result + (0 .. length - 1));
  ensures \fresh(\result, (integer)length * sizeof(int));
  ensures length == 0 || \separated(\result + (0 .. length - 1), a + (0 .. length - 1));
  ensures length == 0 || \separated(\result + (0 .. length - 1), b + (0 .. length - 1));
  ensures \forall integer i; 0 <= i && i < length ==> \result[i] == a[i] % b[i];
*/
int *ElementWiseModulo(const int *a, const int *b, int length)
{
    int *result = alloc_int_array(length, a, b);

    //@ assert result != \null;
    //@ assert length == 0 || \valid(result + (0 .. length - 1));
    //@ assert \fresh(result, (integer)length * sizeof(int));
    //@ assert length == 0 || \separated(result + (0 .. length - 1), a + (0 .. length - 1));
    //@ assert length == 0 || \separated(result + (0 .. length - 1), b + (0 .. length - 1));

    int i = 0;

    /*@
      loop invariant length >= 0;
      loop invariant 0 <= i && i <= length;
      loop invariant result != \null;
      loop invariant length == 0 || \valid(result + (0 .. length - 1));
      loop invariant length == 0 || \valid_read(a + (0 .. length - 1));
      loop invariant length == 0 || \valid_read(b + (0 .. length - 1));
      loop invariant \fresh(result, (integer)length * sizeof(int));
      loop invariant length == 0 || \separated(result + (0 .. length - 1), a + (0 .. length - 1));
      loop invariant length == 0 || \separated(result + (0 .. length - 1), b + (0 .. length - 1));
      loop invariant \forall integer k; 0 <= k && k < length ==> b[k] != 0;
      loop invariant \forall integer k; 0 <= k && k < length ==> !(a[k] == INT_MIN && b[k] == -1);
      loop invariant \forall integer k; 0 <= k && k < i ==> result[k] == a[k] % b[k];
      loop assigns i, result[0 .. length - 1];
      loop variant length - i;
    */
    while (i < length) {
        int idx = i;

        //@ assert 0 <= idx;
        //@ assert idx < length;
        //@ assert idx < INT_MAX;
        //@ assert \valid_read(a + idx);
        //@ assert \valid_read(b + idx);
        //@ assert \valid(result + idx);
        //@ assert b[idx] != 0;
        //@ assert !(a[idx] == INT_MIN && b[idx] == -1);
        //@ assert \forall integer k; 0 <= k && k < idx ==> result[k] == a[k] % b[k];

        result[idx] = a[idx] % b[idx];

        //@ assert result[idx] == a[idx] % b[idx];
        //@ assert \forall integer k; 0 <= k && k < idx ==> result[k] == a[k] % b[k];
        //@ assert \forall integer k; 0 <= k && k < idx + 1 ==> (k < idx || k == idx);
        //@ assert \forall integer k; 0 <= k && k < idx + 1 ==> result[k] == a[k] % b[k];

        i = idx + 1;

        //@ assert i == idx + 1;
        //@ assert \forall integer k; 0 <= k && k < i ==> result[k] == a[k] % b[k];
    }

    //@ assert i == length;
    //@ assert \forall integer k; 0 <= k && k < length ==> result[k] == a[k] % b[k];

    return result;
}