#include <limits.h>

#define MAX_NUMS 100
#define MAX_DIGITS 10
#define STRIDE (MAX_DIGITS + 1)

/*@
  requires x >= 0;
  assigns \nothing;
  ensures 1 <= \result && \result <= MAX_DIGITS;
  ensures x == 0 ==> \result == 1;
*/
int digit_count_int(int x) {
  if (x < 10) {
    return 1;
  }
  if (x < 100) {
    return 2;
  }
  if (x < 1000) {
    return 3;
  }
  if (x < 10000) {
    return 4;
  }
  if (x < 100000) {
    return 5;
  }
  if (x < 1000000) {
    return 6;
  }
  if (x < 10000000) {
    return 7;
  }
  if (x < 100000000) {
    return 8;
  }
  if (x < 1000000000) {
    return 9;
  }
  return 10;
}

/*@
  requires x >= 0;
  requires \valid(buf + (0 .. MAX_DIGITS));
  assigns buf[0 .. MAX_DIGITS];
  ensures 1 <= \result && \result <= MAX_DIGITS;
  ensures buf[\result] == '\0';
  ensures \forall integer i; 0 <= i && i < \result ==> '0' <= buf[i] && buf[i] <= '9';
  ensures x == 0 ==> \result == 1 && buf[0] == '0';
*/
int int_to_decimal(int x, char *buf) {
  int len = digit_count_int(x);

  buf[len] = '\0';

  if (x == 0) {
    buf[0] = '0';
    return len;
  }

  int y = x;
  int i = len - 1;

  /*@
    loop invariant -1 <= i && i < len;
    loop invariant y >= 0;
    loop invariant \forall integer k; i < k && k < len ==> '0' <= buf[k] && buf[k] <= '9';
    loop assigns i, y, buf[0 .. len - 1];
    loop variant i + 1;
  */
  while (i >= 0) {
    //@ assert 0 <= y % 10;
    //@ assert y % 10 <= 9;
    buf[i] = (char)('0' + (y % 10));
    //@ assert '0' <= buf[i];
    //@ assert buf[i] <= '9';
    y = y / 10;
    i = i - 1;
  }

  return len;
}

/*@
  requires 1 <= la && la <= MAX_DIGITS;
  requires 1 <= lb && lb <= MAX_DIGITS;
  requires \valid_read(a + (0 .. la - 1));
  requires \valid_read(b + (0 .. lb - 1));
  assigns \nothing;
  ensures \result == -1 || \result == 0 || \result == 1;
*/
int concat_cmp(const char *a, int la, const char *b, int lb) {
  int k = 0;
  int total = la + lb;

  /*@
    loop invariant 0 <= k && k <= total;
    loop invariant total == la + lb;
    loop assigns k;
    loop variant total - k;
  */
  while (k < total) {
    char ca;
    char cb;

    if (k < la) {
      ca = a[k];
    } else {
      ca = b[k - la];
    }

    if (k < lb) {
      cb = b[k];
    } else {
      cb = a[k - lb];
    }

    if (ca > cb) {
      return 1;
    }

    if (ca < cb) {
      return -1;
    }

    k = k + 1;
  }

  return 0;
}

/*@
  requires 0 <= n && n <= MAX_NUMS;
  requires n == 0 || \valid_read(nums + (0 .. n - 1));
  requires \forall integer i; 0 <= i && i < n ==> nums[i] >= 0;
  requires out_cap >= n * MAX_DIGITS + 1;
  requires out_cap >= 2;
  requires \valid(out + (0 .. out_cap - 1));
  requires n == 0 || \separated(nums + (0 .. n - 1), out + (0 .. out_cap - 1));
  assigns out[0 .. out_cap - 1];
  ensures 1 <= \result && \result < out_cap;
  ensures out[\result] == '\0';
  ensures n == 0 ==> \result == 1 && out[0] == '0';
  ensures (\forall integer i; 0 <= i && i < n ==> nums[i] == 0) ==> \result == 1 && out[0] == '0';
*/
int largestNumber(const int *nums, int n, char *out, int out_cap) {
  char strs[MAX_NUMS * STRIDE];
  int lens[MAX_NUMS];

  int all_zero = 1;
  int i = 0;

  /*@
    loop invariant 0 <= i && i <= n;
    loop invariant all_zero == 0 || all_zero == 1;
    loop invariant all_zero == 1 ==> (\forall integer k; 0 <= k && k < i ==> nums[k] == 0);
    loop invariant (\forall integer k; 0 <= k && k < i ==> nums[k] == 0) ==> all_zero == 1;
    loop invariant all_zero == 0 ==> 0 < i;
    loop invariant \forall integer k; 0 <= k && k < i ==> 1 <= lens[k] && lens[k] <= MAX_DIGITS;
    loop assigns i, all_zero, lens[0 .. MAX_NUMS - 1], strs[0 .. MAX_NUMS * STRIDE - 1];
    loop variant n - i;
  */
  while (i < n) {
    lens[i] = int_to_decimal(nums[i], strs + i * STRIDE);

    if (nums[i] != 0) {
      all_zero = 0;
    }

    i = i + 1;
  }

  //@ assert i == n;

  if (all_zero == 1) {
    out[0] = '0';
    out[1] = '\0';
    return 1;
  }

  //@ assert all_zero == 0;
  //@ assert n > 0;

  int pass = 0;
  int j = 0;
  int k = 0;
  int temp_len = 0;
  char tmp = '\0';

  /*@
    loop invariant 0 <= pass && pass <= n;
    loop invariant \forall integer t; 0 <= t && t < n ==> 1 <= lens[t] && lens[t] <= MAX_DIGITS;
    loop assigns pass, j, k, temp_len, tmp, lens[0 .. MAX_NUMS - 1], strs[0 .. MAX_NUMS * STRIDE - 1];
    loop variant n - pass;
  */
  while (pass < n) {
    j = 0;

    /*@
      loop invariant 0 <= j && j + 1 <= n - pass;
      loop invariant \forall integer t; 0 <= t && t < n ==> 1 <= lens[t] && lens[t] <= MAX_DIGITS;
      loop assigns j, k, temp_len, tmp, lens[0 .. MAX_NUMS - 1], strs[0 .. MAX_NUMS * STRIDE - 1];
      loop variant n - pass - 1 - j;
    */
    while (j + 1 < n - pass) {
      if (concat_cmp(strs + j * STRIDE, lens[j], strs + (j + 1) * STRIDE, lens[j + 1]) < 0) {
        temp_len = lens[j];
        lens[j] = lens[j + 1];
        lens[j + 1] = temp_len;

        k = 0;

        /*@
          loop invariant 0 <= k && k <= STRIDE;
          loop assigns k, tmp, strs[0 .. MAX_NUMS * STRIDE - 1];
          loop variant STRIDE - k;
        */
        while (k < STRIDE) {
          tmp = strs[j * STRIDE + k];
          strs[j * STRIDE + k] = strs[(j + 1) * STRIDE + k];
          strs[(j + 1) * STRIDE + k] = tmp;
          k = k + 1;
        }
      }

      j = j + 1;
    }

    pass = pass + 1;
  }

  int pos = 0;
  i = 0;
  j = 0;

  /*@
    loop invariant 0 <= i && i <= n;
    loop invariant 0 <= pos && pos <= i * MAX_DIGITS;
    loop invariant i <= pos;
    loop invariant \forall integer t; 0 <= t && t < n ==> 1 <= lens[t] && lens[t] <= MAX_DIGITS;
    loop assigns i, j, pos, out[0 .. out_cap - 1];
    loop variant n - i;
  */
  while (i < n) {
    j = 0;

    /*@
      loop invariant 0 <= j && j <= lens[i];
      loop invariant 0 <= pos && pos <= i * MAX_DIGITS + j;
      loop invariant i + j <= pos;
      loop invariant \forall integer t; 0 <= t && t < n ==> 1 <= lens[t] && lens[t] <= MAX_DIGITS;
      loop assigns j, pos, out[0 .. out_cap - 1];
      loop variant lens[i] - j;
    */
    while (j < lens[i]) {
      out[pos] = strs[i * STRIDE + j];
      pos = pos + 1;
      j = j + 1;
    }

    i = i + 1;
  }

  //@ assert pos <= n * MAX_DIGITS;
  //@ assert pos < out_cap;
  //@ assert pos >= n;
  //@ assert pos >= 1;

  out[pos] = '\0';
  return pos;
}