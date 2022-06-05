/* Preliminaries */
setCounterClass =
  lambda r:{x:Ref Nat}.
  lambda self:Unit->{get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit}.
    lambda _:Unit. {
      get = lambda _:Unit. !(r.x),
      set = lambda i:Nat. r.x := i,
      inc = lambda _:Unit. (self unit).set(succ((self unit).get unit))
    };

/* Problem 1 */
instrCounterClass =
  lambda r:{x:Ref Nat, a:Ref Nat}.
  lambda self:Unit->{get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit, accesses:Unit->Nat}.
    lambda _:Unit.
      let super = setCounterClass r self unit in {
        get = lambda _:Unit. (r.a := succ(!(r.a)); super.get unit),
        set = lambda i:Nat. (r.a := succ(!(r.a)); super.set i),
        inc = super.inc,
        accesses = lambda _:Unit. !(r.a)
    };

newInstrCounter =
  lambda _:Unit. let r = {x=ref 1, a=ref 0} in
    fix (instrCounterClass r) unit;

ic = newInstrCounter unit;
(ic.set 5; ic.accesses unit);

(ic.inc unit; ic.get unit);
ic.accesses unit;

/* Problem 2 */
resetInstrCounterClass =
  lambda r:{x:Ref Nat, a:Ref Nat}.
  lambda self:Unit->{get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit, accesses:Unit->Nat, reset:Unit->Unit}.
    lambda _:Unit.
      let super = instrCounterClass r self unit in {
        get = super.get,
        set = super.set,
        inc = super.inc,
        accesses = super.accesses,
        reset = lambda _:Unit. r.x := 1
      };

newResetInstrCounterClass =
  lambda _:Unit. let r = {x=ref 1, a=ref 0} in
    fix (resetInstrCounterClass r) unit;

rc = newResetInstrCounterClass unit;
rc.accesses unit;
(rc.inc unit; rc.accesses unit);
(rc.reset unit; rc.get unit);
rc.accesses unit;

/* Problem 3 */
backupInstrCounterClass =
  lambda r:{x:Ref Nat, a:Ref Nat, b:Ref Nat}.
    lambda self:Unit->{get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit, accesses:Unit->Nat, reset:Unit->Unit, backup:Unit->Unit}.
      lambda _:Unit.
        let super = resetInstrCounterClass r self unit in {
          get = super.get,
          set = super.set,
          inc = super.inc,
          accesses = super.accesses,
          reset = lambda _:Unit. r.x := !(r.b),
          backup = lambda _:Unit. r.b := !(r.x)
        };

newBackupInstrCounterClass =
  lambda _:Unit. let r = {x=ref 1, a=ref 0, b=ref 1} in
    fix (backupInstrCounterClass r) unit;

bc = newBackupInstrCounterClass unit;
bc.accesses unit;
(bc.inc unit; bc.inc unit; bc.get unit);
(bc.backup unit; bc.set 10; bc.get unit);
(bc.reset unit; bc.get unit);
bc.accesses unit;