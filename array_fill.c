/*@ requires \valid(val+(0..n-1));
  requires n > 0;

  ensures \forall integer j; 0 <= j < n ==> val[j] == value;
  assigns val[0..n-1];
  */
void array_fill (int value, int val[], int n) {
  int i;
  /*@ loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0 <= j < i ==> val[j] == value;
    loop variant n - i;
    */
  for(i = 0; i < n; i++) {
    val[i] = value;
  }
}
