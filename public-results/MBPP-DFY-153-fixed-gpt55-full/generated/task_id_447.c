#include <limits.h>

typedef struct {
  int length;
  int *data;
} IntArray;

/*@
  requires \valid_read(a);
  requires \valid(cubed);
  requires 0 <= a->length;
  requires a->length == 0 || \valid_read(a->data + (0 .. a->length - 1));
  requires a->length == 0 || \valid(cubed->data + (0 .. a->length - 1));
  requires \separated(a, cubed);
  requires a->length == 0 || \separated(a->data + (0 .. a->length - 1), cubed->data + (0 .. a->length - 1));
  requires a->length == 0 || \separated(a, cubed->data + (0 .. a->length - 1));
  requires a->length == 0 || \separated(cubed, a->data + (0 .. a->length - 1));
  requires a->length == 0 || \separated(cubed, cubed->data + (0 .. a->length - 1));
  requires \forall integer i; 0 <= i && i < a->length ==> INT_MIN <= a->data[i] * a->data[i] * a->data[i];
  requires \forall integer i; 0 <= i && i < a->length ==> a->data[i] * a->data[i] * a->data[i] <= INT_MAX;

  assigns cubed->length, cubed->data[0 .. a->length - 1];

  ensures cubed->length == a->length;
  ensures \forall integer i; 0 <= i && i < a->length ==> cubed->data[i] == a->data[i] * a->data[i] * a->data[i];
*/
void CubeElements(const IntArray *a, IntArray *cubed)
{
  int n = a->length;
  const int *in = a->data;
  int *out = cubed->data;

  cubed->length = n;

  int i;

  /*@
    loop invariant 0 <= i && i <= n;
    loop invariant n == a->length;
    loop invariant in == a->data;
    loop invariant out == cubed->data;
    loop invariant cubed->length == n;
    loop invariant n == 0 || \valid_read(in + (0 .. n - 1));
    loop invariant n == 0 || \valid(out + (0 .. n - 1));
    loop invariant n == 0 || \separated(in + (0 .. n - 1), out + (0 .. n - 1));
    loop invariant n == 0 || \separated(a, out + (0 .. n - 1));
    loop invariant n == 0 || \separated(cubed, out + (0 .. n - 1));
    loop invariant \forall integer k; 0 <= k && k < i ==> out[k] == in[k] * in[k] * in[k];
    loop assigns i, out[0 .. n - 1];
    loop variant n - i;
  */
  for (i = 0; i < n; i++) {
    //@ assert INT_MIN <= in[i] * in[i] * in[i];
    //@ assert in[i] * in[i] * in[i] <= INT_MAX;
    long long x = (long long)in[i];
    long long value = x * x * x;
    out[i] = (int)value;
    //@ assert out[i] == in[i] * in[i] * in[i];
    //@ assert \forall integer k; 0 <= k && k < i ==> out[k] == in[k] * in[k] * in[k];
    //@ assert \forall integer k; 0 <= k && k < i + 1 ==> (k < i || k == i);
    //@ assert \forall integer k; 0 <= k && k < i + 1 && k < i ==> out[k] == in[k] * in[k] * in[k];
    //@ assert \forall integer k; 0 <= k && k < i + 1 && k == i ==> out[k] == in[k] * in[k] * in[k];
    //@ assert \forall integer k; 0 <= k && k < i + 1 ==> out[k] == in[k] * in[k] * in[k];
  }
}