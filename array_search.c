/*@ requires n > 0;
  requires \valid(t+(0..n-1));

  behavior success:
  assumes \exists integer j; 0 <= j < n && t[j] == val;
  ensures \exists integer j; 0 <= j < n && t[j] == val && \result == j;

  behavior failure:
  assumes \forall integer j; 0 <= j < n ==> t[j] != val;
  ensures \result == -1;
  */
int array_search (int val, int t[], int n) {
  int i;
  /*@ loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0 <= j < i ==> t[j] != val;
    loop variant n - i;
    */
  for (i = 0; i < n; i++) {
    if (t[i] == val) {
      return i;
    }
  }
  return -1;
}
