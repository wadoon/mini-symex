function fib(n: int): int;
var
  a: int;
  b: int;
pre n >= 0
post fib > 0
begin
  fib := 0;
  if n = 0 or n = 1
  then fib := 1
  else
  begin
    a := fib(n - 1);
    b := fib(n - 2);
    fib := a + b;
  end;
end

procedure main();
var
  n: int;
  y: int;
pre true
post (y > 0)
begin
  n := 0;
  havoc(n);
  assume(n >= 0);
  y = fib(n);
end
