/*@ requires n > 0;
  requires \valid(a+(0..n-1));
  requires \valid(b+(0..n-1));

  behavior success:
  assumes
  \forall integer j; 0 <= j < n ==> a[j] == b[j];
  ensures \result == 0;

  behavior failure:
  assumes
  \exists integer j; 0 <= j < n && a[j] != b[j];
  ensures \result == -1;
  */
int compare (int a[], int b[], int n) {
  int i;
  /*@ loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0 <= j < i ==> a[j] == b[j];
    loop variant n - i;
    */
  for (i = 0; i < n; i++) {
    if (a[i] != b[i]) {
      return -1;
    }
  }
  return 0;
}
