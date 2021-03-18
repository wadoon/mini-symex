procedure main();
var
  a: int;
begin
  a := 0;
  havoc(a);
  assume(a % 2 = 0);
  while true
   invariant a % 2 = 0
   modifies  a
  do
      a := a + 2
end