void main() {
  int a = 1;
  int b = 0;
  havoc b;
  assert a == 1;
  if(b == 0)
    a = a + 2;
  else
    a = a + 4;
  assert a != 1;
}