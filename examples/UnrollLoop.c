void main() {
  int[] arr;
  int i = 0;
  l1: while( i < 5) {
    arr[i] = i;
    i = i + 1;
  }
  assert (\forall int i; 0 <= i && i < 5 ==> arr[i] == i);
}