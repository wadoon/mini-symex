function BinarySearch(X: int; A: int[]): int;
var
  L, R, I, Cur: int;
  run : bool;
begin
  run := true;
  result := -1;
  if Length(A) <> 0 then
  begin
      L := 0; R := Length(A) - 1;
      while L <= R && run
      do
      begin
        I := L + (R - L) div 2;
        Cur := A[I];
        if X = Cur then
        begin
          run := false;
          result := I;
        end;
        if X > Cur then
          L := I + 1
        else
          R := I - 1;
      end
  end
end