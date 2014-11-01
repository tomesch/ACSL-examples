/*@ requires n > 0;
  requires \valid(t+(0..n-1));

  ensures \forall integer j; 0 <= j < n ==> t[\result] <= t[j];
  ensures 0 <= \result < n; 
  */
int min (int t[], int n) {
  int i, min = 0;
  /*@ loop invariant 0 <= i <= n;
    loop invariant 0 <= min < n;
    loop invariant \forall integer j; 0 <= j < i ==> t[min] <= t[j];
    loop variant n - i;
    */
  for (i = 0; i < n; i++) {
    if (t[i] < t[min]) {
      min = i;
    }
  }
  return min;
}
