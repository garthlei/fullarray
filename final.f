isLess = fix (lambda f:Nat->Nat->Bool. lambda x:Nat. lambda y: Nat.
  if iszero x then
    if iszero y then false else true
  else if iszero y then false
  else f (pred x) (pred y));

sortThree = lambda a:Array Nat.
  (if isLess (!(a[1])) (!(a[0])) then
    let t = !(a[0]) in
    (a[0] := !(a[1]); a[1] := t)
  else unit;
  if isLess (!(a[2])) (!(a[0])) then
    let t = !(a[0]) in
    (a[0] := !(a[2]); a[2] := t)
  else unit;
  if isLess (!(a[2])) (!(a[1])) then
    let t = !(a[1]) in
    (a[1] := !(a[2]); a[2] := t)
  else unit);

t = Array[Nat](3,50);
!(t[0]);
!(t[1]);
!(t[2]);
(t[0] := 3; t[1] := 2; t[2] := 1);
!(t[0]);
!(t[1]);
!(t[2]);
sortThree t;
t[0];
!(t[0]);
!(t[1]);
!(t[2]);

/* Errors */
t[4];
!(t[4]);
sortThree (Array[Nat](2,0));
