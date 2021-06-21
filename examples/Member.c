int searchGolden(int[]  haystack, int needle) {
  choose x : haystack[x] == needle && x < length && x > 0;
  return x;
}

int search(int[]  haystack, int needle, int length) {
  int i = 0;
  int res = -1;
  while(i < length) {
    if(haystack[x]==needle) {
      res = i;
    }
    i++;
  }
  return res;
}