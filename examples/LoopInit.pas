procedure main()
var  i : int; a : int[];
pre true
post (\forall y:int; 0 <= y and  y < 10 ==> a[y] = y)
begin
    i := 0;    
    while( i < 10 )  
    invariant a % 2 = 0
    variant i, a
    do
    begin
        a[i] := i;
        i := i + 1;
    end
end