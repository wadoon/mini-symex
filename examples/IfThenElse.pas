procedure main();
var
  a: int;
  b: int;
begin
  a := 1;
  b := 0;
  havoc(b);
  assert(a = 1);
  if b = 0 then
    a := a + 2
  else
    a := a + 4;

  assert(a <> 1);
end