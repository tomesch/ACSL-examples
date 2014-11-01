/*@ requires \valid(t+(0..n-1));
  requires \valid(s+(0..n-1));
  requires n > 0;

  ensures \forall integer j; 0 <= j < n ==> s[j] == t[j];
  assigns t[0..n-1];
  */
void array_copy (int s[], int t[], int n) {
  int i;
  /*@ loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0 <= j < i ==> t[j] == s[j];
    loop variant n - i;   
    */
  for (i = 0; i < n; i++) {
    t[i] = s[i];
  }
}
