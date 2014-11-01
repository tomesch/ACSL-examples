/*@ requires a && b;
  ensures \result == a || \result == b;
  ensures \result == \min(a, b);
  */
int min(int a, int b) {
  if (a < b) {
    return a;
  }
  else {
    return b;
  }
}
