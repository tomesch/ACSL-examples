/*@ requires \valid(t+(0..n-1));
  requires n > 0;

  behavior is_all_zero:
  assumes \forall integer i; 0 <= i < n ==> t[i] == 0;
  ensures \result == 0;

  behavior is_not_all_zero:
  assumes \exists integer k; 0 <= k < n && t[k] != 0;
  ensures \result == -1;
  */
int all_zeros(int t[], int n) {
  int i;
  /*@ loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0<= j < i ==> t[j] == 0;
    loop variant n - i;
    */
  for (i = 0; i < n; i++) {
    if (t[i] != 0) {
      return -1;
    }
  }
  return 0;
}
