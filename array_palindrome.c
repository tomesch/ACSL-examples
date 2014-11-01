/*@ requires n > 0;
  requires \valid(t+(0..n-1));

  behavior success:
  assumes
  \forall integer j; 0 <= j < n ==> t[j] == t[n - j - 1];
  ensures \result == 0;

  behavior failure:
  assumes
  \exists integer j; 0 <= j < n && t[j] != t[n - j - 1];
  ensures \result == -1;
  */
int palindrome (int t[], int n) {
  int i;
  /*@ loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0 <= j < i ==> t[j] == t[n - j - 1];
    loop variant n - i;
    */
  for (i = 0; i < n; i++) {
    if (t[i] != t[n - i - 1]) {
      return -1;
    }
  }
  return 0;
}
