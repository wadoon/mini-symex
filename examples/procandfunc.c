
int awayfromzero(int x) {
  if(x < 0)
    return x - 1;
  else
    return x + 1;
}

int a = 25;

void test() {
  int b = awayfromzero(a);
  assert(b > a);
}

void main() {
 test();
}