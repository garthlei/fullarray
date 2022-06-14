open Format
open Syntax
open Support.Error
open Support.Pervasive

(* ------------------------   EVALUATION  ------------------------ *)

let rec isnumericval ctx t = match t with
    TmZero(_) -> true
  | TmSucc(_,t1) -> isnumericval ctx t1
  | _ -> false

let rec isval ctx t = match t with
    TmString _  -> true
  | TmUnit(_)  -> true
  | TmLoc(_,_) -> true
  | TmArrayLoc(_,_) -> true
  | TmTag(_,l,t1,_) -> isval ctx t1
  | TmTrue(_)  -> true
  | TmFalse(_) -> true
  | TmFloat _  -> true
  | t when isnumericval ctx t  -> true
  | TmAbs(_,_,_,_) -> true
  | TmRecord(_,fields) -> List.for_all (fun (l,ti) -> isval ctx ti) fields
  | _ -> false

type store = term list
type arrstore = int list list
let emptystore = []
let emptyarrstore = []
let extendstore store v = (List.length store, List.append store [v])
let lookuploc store l = List.nth store l
let updatestore store n v =
  let rec f s = match s with 
      (0, v'::rest) -> v::rest
    | (n, v'::rest) -> v' :: (f (n-1,rest))
    | _ -> error dummyinfo "updatestore: bad index"
  in
    f (n,store)
let shiftstore i store = List.map (fun t -> termShift i t) store 
let arraylen arrstore a = List.length (List.nth arrstore a)
let dbg = true

exception NoRuleApplies

let rec eval1 ctx store arrstore t = match t with
    TmApp(_,TmError(fi),t2) ->
      TmError(fi), store, arrstore
  | TmApp(_,v1,TmError(fi)) when isval ctx v1 ->
      TmError(fi), store, arrstore
  | TmApp(fi,TmAbs(_,x,tyT11,t12),v2) when isval ctx v2 ->
      termSubstTop v2 t12, store, arrstore
  | TmApp(fi,v1,t2) when isval ctx v1 ->
      let t2',store',arrstore' = eval1 ctx store arrstore t2 in
      TmApp(fi, v1, t2'), store', arrstore'
  | TmApp(fi,t1,t2) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmApp(fi, t1', t2), store', arrstore'
  | TmAscribe(_,TmError(fi),tyT) ->
      TmError(fi), store, arrstore
  | TmAscribe(fi,v1,tyT) when isval ctx v1 ->
      v1, store, arrstore
  | TmAscribe(fi,t1,tyT) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmAscribe(fi,t1',tyT), store', arrstore'
  | TmRef(_,TmError(fi)) ->
      TmError(fi), store, arrstore
  | TmRef(fi,t1) ->
      if not (isval ctx t1) then
        let (t1',store',arrstore') = eval1 ctx store arrstore t1
        in (TmRef(fi,t1'), store', arrstore')
      else
        let (l,store') = extendstore store t1 in
        (TmLoc(dummyinfo,l), store', arrstore)
  | TmDeref(_,TmError(fi)) ->
      TmError(fi), store, arrstore
  | TmDeref(fi,t1) ->
      if not (isval ctx t1) then
        let (t1',store',arrstore') = eval1 ctx store arrstore t1
        in (TmDeref(fi,t1'), store', arrstore')
      else (match t1 with
            TmLoc(_,l) -> (lookuploc store l, store, arrstore)
          | _ -> raise NoRuleApplies)
  | TmArray(_,_,TmError(fi),t2) ->
      TmError(fi), store, arrstore
  | TmArray(_,_,v1,TmError(fi)) when isval ctx v1 ->
      TmError(fi), store, arrstore
  | TmArray(fi,tyT,v1,v2) when (isnumericval ctx v1) && (isval ctx v2) ->
      let rec extendstorearr t cnt store ls = (match cnt with
        TmSucc(_,t1) ->
          let (l, store') = extendstore store t in
          extendstorearr t t1 store' (List.append ls [l])
      | TmZero(_) -> (ls, store)
      | _ -> raise NoRuleApplies) in
      let (ls, store') = extendstorearr v2 v1 store [] in
      let (a, arrstore') = extendstore arrstore ls in
      (TmArrayLoc(dummyinfo,a), store', arrstore')
  | TmArray(fi,tyT,v1,t2) when isval ctx v1 ->
      let (t2',store',arrstore') = eval1 ctx store arrstore t2 in
      TmArray(fi,tyT,v1,t2'), store', arrstore'
  | TmArray(fi,tyT,t1,t2) ->
      let (t1',store',arrstore') = eval1 ctx store arrstore t1 in
      TmArray(fi,tyT,t1',t2), store', arrstore'
  | TmArrayIdx(_,TmError(fi),t2) ->
      TmError(fi), store, arrstore
  | TmArrayIdx(_,v1,TmError(fi)) when isval ctx v1 ->
      TmError(fi), store, arrstore
  | TmArrayIdx(fi,v1,v2) when (isval ctx v1) && (isval ctx v2) ->
      let rec getlitval t = (match t with
        TmSucc(_,t1) -> (getlitval t1) + 1
      | TmZero(_) -> 0
      | _ -> raise NoRuleApplies) in
      let litvalue = getlitval v2 in
      (match v1 with
        TmArrayLoc(_,a) -> 
        let arraylen = arraylen arrstore a in
        if litvalue < arraylen then
          TmLoc(dummyinfo, List.nth (lookuploc arrstore a) litvalue),
          store, arrstore
        else TmError(dummyinfo), store, arrstore
      | _ -> raise NoRuleApplies)
  | TmArrayIdx(fi,v1,t2) when isval ctx v1 ->
      let (t2',store',arrstore') = eval1 ctx store arrstore t2 in
      TmArrayIdx(fi,v1,t2'), store', arrstore'
  | TmArrayIdx(fi,t1,t2) ->
      let (t1',store',arrstore') = eval1 ctx store arrstore t1 in
      TmArrayIdx(fi,t1',t2), store', arrstore'
  | TmAssign(fi,t1,t2) ->
      if not (isval ctx t1) then
        (match t1 with
          TmError(fi1) -> TmError(fi1), store, arrstore
        | _ -> let (t1',store',arrstore') = eval1 ctx store arrstore t1
            in (TmAssign(fi,t1',t2), store', arrstore'))
      else if not (isval ctx t2) then
        (match t2 with
          TmError(fi1) -> TmError(fi1), store, arrstore
        | _ -> let (t2',store',arrstore') = eval1 ctx store arrstore t2
            in (TmAssign(fi,t1,t2'), store', arrstore'))
      else (match t1 with
            TmLoc(_,l) -> (TmUnit(dummyinfo), updatestore store l t2, arrstore)
          | _ -> raise NoRuleApplies)
  | TmTag(_,_,TmError(fi),tyT) -> TmError(fi), store, arrstore
  | TmTag(fi,l,t1,tyT) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmTag(fi, l, t1',tyT), store', arrstore'
  | TmCase(_,TmError(fi),branches) -> TmError(fi), store, arrstore
  | TmCase(fi,TmTag(_,li,v11,_),branches) when isval ctx v11->
      (try 
         let (x,body) = List.assoc li branches in
         termSubstTop v11 body, store, arrstore
       with Not_found -> raise NoRuleApplies)
  | TmCase(fi,t1,branches) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmCase(fi, t1', branches), store', arrstore'
  | TmLet(_,_,TmError(fi),t2) -> TmError(fi), store, arrstore
  | TmLet(fi,x,v1,t2) when isval ctx v1 ->
      (match t2 with
        TmError(fi1) -> TmError(fi1), store, arrstore
      | _ -> termSubstTop v1 t2, store, arrstore)
  | TmLet(fi,x,t1,t2) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmLet(fi, x, t1', t2), store', arrstore'
  | TmFix(_,TmError(fi)) -> TmError(fi), store, arrstore
  | TmFix(fi,v1) as t when isval ctx v1 ->
      (match v1 with
         TmAbs(_,_,_,t12) -> termSubstTop t t12, store, arrstore
       | _ -> raise NoRuleApplies)
  | TmFix(fi,t1) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1
      in TmFix(fi,t1'), store', arrstore'
  | TmIf(_,TmError(fi),t2,t3) -> TmError(fi), store, arrstore
  | TmIf(_,TmTrue(_),t2,t3) ->
      t2, store, arrstore
  | TmIf(_,TmFalse(_),t2,t3) ->
      t3, store, arrstore
  | TmIf(fi,t1,t2,t3) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmIf(fi, t1', t2, t3), store', arrstore'
  | TmTimesfloat(fi,TmFloat(_,f1),TmFloat(_,f2)) ->
      TmFloat(fi, f1 *. f2), store, arrstore
  | TmTimesfloat(fi,(TmFloat(_,f1) as t1),t2) ->
      let t2',store',arrstore' = eval1 ctx store arrstore t2 in
      TmTimesfloat(fi,t1,t2') , store', arrstore'
  | TmTimesfloat(fi,t1,t2) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmTimesfloat(fi,t1',t2) , store', arrstore'
  | TmVar(fi,n,_) ->
      (match getbinding fi ctx n with
          TmAbbBind(t,_) -> t,store,arrstore
        | _ -> raise NoRuleApplies)
  | TmRecord(fi,fields) ->
      let rec evalafield l = match l with 
        [] -> raise NoRuleApplies
      | (l,vi)::rest when isval ctx vi -> 
          let rest',store',arrstore' = evalafield rest in
          (l,vi)::rest', store', arrstore'
      | (l,ti)::rest -> 
          let ti',store',arrstore' = eval1 ctx store arrstore ti in
          (l, ti')::rest, store', arrstore'
      in let fields',store',arrstore' = evalafield fields in
      TmRecord(fi, fields'), store', arrstore'
  | TmProj(fi, TmRecord(_, fields), l) ->
      (try List.assoc l fields, store, arrstore
       with Not_found -> raise NoRuleApplies)
  | TmProj(fi, t1, l) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmProj(fi, t1', l), store', arrstore'
  | TmSucc(_,TmError(fi)) -> TmError(fi), store, arrstore
  | TmSucc(fi,t1) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmSucc(fi, t1'), store', arrstore'
  | TmPred(_,TmError(fi)) -> TmError(fi), store, arrstore
  | TmPred(_,TmZero(_)) ->
      TmZero(dummyinfo), store, arrstore
  | TmPred(_,TmSucc(_,nv1)) when (isnumericval ctx nv1) ->
      nv1, store, arrstore
  | TmPred(fi,t1) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmPred(fi, t1'), store', arrstore
  | TmIsZero(_,TmError(fi)) -> TmError(fi), store, arrstore
  | TmIsZero(_,TmZero(_)) ->
      TmTrue(dummyinfo), store, arrstore
  | TmIsZero(_,TmSucc(_,nv1)) when (isnumericval ctx nv1) ->
      TmFalse(dummyinfo), store, arrstore
  | TmIsZero(fi,t1) ->
      let t1',store',arrstore' = eval1 ctx store arrstore t1 in
      TmIsZero(fi, t1'), store', arrstore'
  | _ -> 
      raise NoRuleApplies
  (* TODO Error with Proj and float *)

let rec eval ctx store arrstore t =
  try let t',store',arrstore' = eval1 ctx store arrstore t
      in eval ctx store' arrstore' t'
  with NoRuleApplies -> t,store,arrstore

(* ------------------------   SUBTYPING  ------------------------ *)

let evalbinding ctx store arrstore b = match b with
    TmAbbBind(t,tyT) ->
      let t',store',arrstore' = eval ctx store arrstore t in 
      TmAbbBind(t',tyT), store', arrstore'
  | bind -> bind,store,arrstore

let istyabb ctx i = 
  match getbinding dummyinfo ctx i with
    TyAbbBind(tyT) -> true
  | _ -> false

let gettyabb ctx i = 
  match getbinding dummyinfo ctx i with
    TyAbbBind(tyT) -> tyT
  | _ -> raise NoRuleApplies

let rec computety ctx tyT = match tyT with
    TyVar(i,_) when istyabb ctx i -> gettyabb ctx i
  | _ -> raise NoRuleApplies

let rec simplifyty ctx tyT =
  try
    let tyT' = computety ctx tyT in
    simplifyty ctx tyT' 
  with NoRuleApplies -> tyT

let rec tyeqv ctx tyS tyT =
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyVariant(fields1),TyVariant(fields2)) ->
       (List.length fields1 = List.length fields2)
       && List.for_all2
            (fun (li1,tyTi1) (li2,tyTi2) ->
               (li1=li2) && tyeqv ctx tyTi1 tyTi2)
            fields1 fields2
  | (TyBot,TyBot) -> true
  | (TyId(b1),TyId(b2)) -> b1=b2
  | (TyString,TyString) -> true
  | (TyFloat,TyFloat) -> true
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
       (tyeqv ctx tyS1 tyT1) && (tyeqv ctx tyS2 tyT2)
  | (TyUnit,TyUnit) -> true
  | (TyRef(tyT1),TyRef(tyT2)) -> tyeqv ctx tyT1 tyT2
  | (TyArray(tyT1),TyArray(tyT2)) -> tyeqv ctx tyT1 tyT2
  | (TySource(tyT1),TySource(tyT2)) -> tyeqv ctx tyT1 tyT2
  | (TySink(tyT1),TySink(tyT2)) -> tyeqv ctx tyT1 tyT2
  | (TyTop,TyTop) -> true
  | (TyBool,TyBool) -> true
  | (TyNat,TyNat) -> true
  | (TyRecord(fields1),TyRecord(fields2)) -> 
       List.length fields1 = List.length fields2
       &&                                         
       List.for_all 
         (fun (li2,tyTi2) ->
            try let (tyTi1) = List.assoc li2 fields1 in
                tyeqv ctx tyTi1 tyTi2
            with Not_found -> false)
         fields2
  | (TyVar(i,_), _) when istyabb ctx i ->
      tyeqv ctx (gettyabb ctx i) tyT
  | (_, TyVar(i,_)) when istyabb ctx i ->
      tyeqv ctx tyS (gettyabb ctx i)
  | (TyVar(i,_),TyVar(j,_)) -> i=j
  | _ -> false

let rec subtype ctx tyS tyT =
   tyeqv ctx tyS tyT ||
   let tyS = simplifyty ctx tyS in
   let tyT = simplifyty ctx tyT in
   match (tyS,tyT) with
     (TyBot,_) -> 
       true
   | (_,TyTop) -> 
       true
   | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
       (subtype ctx tyT1 tyS1) && (subtype ctx tyS2 tyT2)
   | (TyRef(tyT1),TyRef(tyT2)) ->
       subtype ctx tyT1 tyT2 && subtype ctx tyT2 tyT1
   | (TyRef(tyT1),TySource(tyT2)) ->
       subtype ctx tyT1 tyT2
   | (TySource(tyT1),TySource(tyT2)) ->
       subtype ctx tyT1 tyT2
   | (TyRef(tyT1),TySink(tyT2)) ->
       subtype ctx tyT2 tyT1
   | (TySink(tyT1),TySink(tyT2)) ->
       subtype ctx tyT2 tyT1
   | (TyVariant(fS), TyVariant(fT)) ->
       List.for_all
         (fun (li,tySi) -> 
            try let tyTi = List.assoc li fT in
                subtype ctx tySi tyTi
            with Not_found -> false)
         fS
   | (TyRecord(fS), TyRecord(fT)) ->
       List.for_all
         (fun (li,tyTi) -> 
            try let tySi = List.assoc li fS in
                subtype ctx tySi tyTi
            with Not_found -> false)
         fT
   | (_,_) -> 
       false

let rec join ctx tyS tyT =
  if subtype ctx tyS tyT then tyT else 
  if subtype ctx tyT tyS then tyS else
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      TyArr(meet ctx  tyS1 tyT1, join ctx tyS2 tyT2)
  | (TyRef(tyT1),TyRef(tyT2)) ->
      if subtype ctx tyT1 tyT2 && subtype ctx tyT2 tyT1 
        then TyRef(tyT1)
        else (* Warning: this is incomplete... *)
             TySource(join ctx tyT1 tyT2)
  | (TySource(tyT1),TySource(tyT2)) ->
      TySource(join ctx tyT1 tyT2)
  | (TyRef(tyT1),TySource(tyT2)) ->
      TySource(join ctx tyT1 tyT2)
  | (TySource(tyT1),TyRef(tyT2)) ->
      TySource(join ctx tyT1 tyT2)
  | (TySink(tyT1),TySink(tyT2)) ->
      TySink(meet ctx tyT1 tyT2)
  | (TyRef(tyT1),TySink(tyT2)) ->
      TySink(meet ctx tyT1 tyT2)
  | (TySink(tyT1),TyRef(tyT2)) ->
      TySink(meet ctx tyT1 tyT2)
  | (TyRecord(fS), TyRecord(fT)) ->
      let labelsS = List.map (fun (li,_) -> li) fS in
      let labelsT = List.map (fun (li,_) -> li) fT in
      let commonLabels = 
        List.find_all (fun l -> List.mem l labelsT) labelsS in
      let commonFields = 
        List.map (fun li -> 
                    let tySi = List.assoc li fS in
                    let tyTi = List.assoc li fT in
                    (li, join ctx tySi tyTi))
                 commonLabels in
      TyRecord(commonFields)
  | _ -> 
      TyTop

and meet ctx tyS tyT =
  if subtype ctx tyS tyT then tyS else 
  if subtype ctx tyT tyS then tyT else 
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      TyArr(join ctx tyS1 tyT1, meet ctx tyS2 tyT2)
  | (TyRef(tyT1),TyRef(tyT2)) ->
      if subtype ctx tyT1 tyT2 && subtype ctx tyT2 tyT1 
        then TyRef(tyT1)
        else (* Warning: this is incomplete... *)
             TySource(meet ctx tyT1 tyT2)
  | (TySource(tyT1),TySource(tyT2)) ->
      TySource(meet ctx tyT1 tyT2)
  | (TyRef(tyT1),TySource(tyT2)) ->
      TySource(meet ctx tyT1 tyT2)
  | (TySource(tyT1),TyRef(tyT2)) ->
      TySource(meet ctx tyT1 tyT2)
  | (TySink(tyT1),TySink(tyT2)) ->
      TySink(join ctx tyT1 tyT2)
  | (TyRef(tyT1),TySink(tyT2)) ->
      TySink(join ctx tyT1 tyT2)
  | (TySink(tyT1),TyRef(tyT2)) ->
      TySink(join ctx tyT1 tyT2)
  | (TyRecord(fS), TyRecord(fT)) ->
      let labelsS = List.map (fun (li,_) -> li) fS in
      let labelsT = List.map (fun (li,_) -> li) fT in
      let allLabels = 
        List.append
          labelsS 
          (List.find_all 
            (fun l -> not (List.mem l labelsS)) labelsT) in
      let allFields = 
        List.map (fun li -> 
                    if List.mem li allLabels then
                      let tySi = List.assoc li fS in
                      let tyTi = List.assoc li fT in
                      (li, meet ctx tySi tyTi)
                    else if List.mem li labelsS then
                      (li, List.assoc li fS)
                    else
                      (li, List.assoc li fT))
                 allLabels in
      TyRecord(allFields)
  | _ -> 
      TyBot

(* ------------------------   TYPING  ------------------------ *)

let rec typeof ctx t =
  match t with
    TmVar(fi,i,_) -> getTypeFromContext fi ctx i
  | TmAbs(fi,x,tyT1,t2) ->
      let ctx' = addbinding ctx x (VarBind(tyT1)) in
      let tyT2 = typeof ctx' t2 in
      TyArr(tyT1, typeShift (-1) tyT2)
  | TmApp(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match simplifyty ctx tyT1 with
          TyArr(tyT11,tyT12) ->
            if subtype ctx tyT2 tyT11 then tyT12
            else error fi "parameter type mismatch" 
        | TyBot -> TyBot
        | _ -> error fi "arrow type expected")
  | TmAscribe(fi,t1,tyT) ->
     if subtype ctx (typeof ctx t1) tyT then
       tyT
     else
       error fi "body of as-term does not have the expected type"
  | TmString _ -> TyString
  | TmUnit(fi) -> TyUnit
  | TmRef(fi,t1) ->
      TyRef(typeof ctx t1)
  | TmLoc(fi,l) ->
      error fi "locations are not supposed to occur in source programs!"
  | TmLet(fi,x,t1,t2) ->
     let tyT1 = typeof ctx t1 in
     let ctx' = addbinding ctx x (VarBind(tyT1)) in         
     typeShift (-1) (typeof ctx' t2)
  | TmTrue(fi) -> 
      TyBool
  | TmFalse(fi) -> 
      TyBool
  | TmIf(fi,t1,t2,t3) ->
      if subtype ctx (typeof ctx t1) TyBool then
        join ctx (typeof ctx t2) (typeof ctx t3)
      else error fi "guard of conditional not a boolean"
  | TmRecord(fi, fields) ->
      let fieldtys = 
        List.map (fun (li,ti) -> (li, typeof ctx ti)) fields in
      TyRecord(fieldtys)
  | TmProj(fi, t1, l) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyRecord(fieldtys) ->
            (try List.assoc l fieldtys
             with Not_found -> error fi ("label "^l^" not found"))
        | TyBot -> TyBot
        | _ -> error fi "Expected record type")
  | TmCase(fi, t, cases) ->
      (match simplifyty ctx (typeof ctx t) with
         TyVariant(fieldtys) ->
           List.iter
             (fun (li,(xi,ti)) ->
                try let _ = List.assoc li fieldtys in ()
                with Not_found -> error fi ("label "^li^" not in type"))
             cases;
           let casetypes =
             List.map (fun (li,(xi,ti)) ->
                         let tyTi =
                           try List.assoc li fieldtys
                           with Not_found ->
                             error fi ("label "^li^" not found") in
                         let ctx' = addbinding ctx xi (VarBind(tyTi)) in
                         typeShift (-1) (typeof ctx' ti))
                      cases in
           List.fold_left (join ctx) TyBot casetypes
        | TyBot -> TyBot
        | _ -> error fi "Expected variant type")
  | TmTag(fi, li, ti, tyT) ->
      (match simplifyty ctx tyT with
          TyVariant(fieldtys) ->
            (try
               let tyTiExpected = List.assoc li fieldtys in
               let tyTi = typeof ctx ti in
               if subtype ctx tyTi tyTiExpected
                 then tyT
                 else error fi "field does not have expected type"
             with Not_found -> error fi ("label "^li^" not found"))
        | _ -> error fi "Annotation is not a variant type")
  | TmFix(fi, t1) ->
      let tyT1 = typeof ctx t1 in
      (match simplifyty ctx tyT1 with
           TyArr(tyT11,tyT12) ->
             if subtype ctx tyT12 tyT11 then tyT12
             else error fi "result of body not compatible with domain"
         | TyBot -> TyBot
         | _ -> error fi "arrow type expected")
  | TmDeref(fi,t1) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyRef(tyT1) -> tyT1
        | TyBot -> TyBot
        | TySource(tyT1) -> tyT1
        | _ -> error fi "argument of ! is not a Ref or Source")
  | TmAssign(fi,t1,t2) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyRef(tyT1) ->
            if subtype ctx (typeof ctx t2) tyT1 then
              TyUnit
            else
              error fi "arguments of := are incompatible"
        | TyBot -> let _ = typeof ctx t2 in TyBot
        |TySink(tyT1) ->
            if subtype ctx (typeof ctx t2) tyT1 then
              TyUnit
            else
              error fi "arguments of := are incompatible"
        | _ -> error fi "argument of ! is not a Ref or Sink")
  | TmFloat _ -> TyFloat
  | TmTimesfloat(fi,t1,t2) ->
      if subtype ctx (typeof ctx t1) TyFloat
      && subtype ctx (typeof ctx t2) TyFloat then TyFloat
      else error fi "argument of timesfloat is not a number"
  | TmInert(fi,tyT) ->
      tyT
  | TmZero(fi) ->
      TyNat
  | TmSucc(fi,t1) ->
      if subtype ctx (typeof ctx t1) TyNat then TyNat
      else error fi "argument of succ is not a number"
  | TmPred(fi,t1) ->
      if subtype ctx (typeof ctx t1) TyNat then TyNat
      else error fi "argument of pred is not a number"
  | TmIsZero(fi,t1) ->
      if subtype ctx (typeof ctx t1) TyNat then TyBool
      else error fi "argument of iszero is not a number"
  | TmError(fi) -> TyBot
  | TmArray(fi,tyT,t1,t2) ->
      if (subtype ctx (typeof ctx t1) TyNat)
          && (subtype ctx (typeof ctx t2) tyT) then
        TyArray(tyT)
      else error fi "mismatched type(s) in array initialization"      
  | TmArrayIdx(fi,t1,t2) ->
      if subtype ctx (typeof ctx t2) TyNat then
        let tyT1 = simplifyty ctx (typeof ctx t1) in
        (match tyT1 with
          TyArray(tyT11) -> TyRef(tyT11)
        | _ -> error fi "subscription used on non-array")
      else error fi "subscription is not a number"
  | TmArrayLoc(fi,a) ->
      error fi "array locations are not supposed to occur in source programs!"

(* ---------------------  GARBAGE COLLECTION --------------------- *)

let gceval1 ctx store arrstore t =
  let rec walk llist arrlist t = match t with
    TmAbs(fi,x,tyT1,t2) -> walk llist arrlist t2
  | TmApp(fi,t1,t2) ->
      let llist',arrlist' = walk llist arrlist t1 in
      walk llist' arrlist' t2
  | TmAscribe(fi,t1,tyT1) -> walk llist arrlist t1
  | TmLoc(fi,l) ->
      if not (List.mem l llist) then
        let llist' = l :: llist in
        walk llist' arrlist (lookuploc store l)
      else llist, arrlist
  | TmArrayLoc(fi,a) ->
      if not (List.mem a arrlist) then
        let arrlist' = a :: arrlist in
        List.fold_left (fun (l,al) loc ->
          walk l al (lookuploc store loc)) (llist,arrlist')
            (lookuploc arrstore a)
      else llist, arrlist
  | TmRef(fi,t1) -> walk llist arrlist t1
  | TmDeref(fi,t1) -> walk llist arrlist t1
  | TmAssign(fi,t1,t2) ->
      let llist',arrlist' = walk llist arrlist t1 in
      walk llist' arrlist' t2
  | TmTag(fi,l,t1,tyT) -> walk llist arrlist t1
  | TmCase(fi,t,cases) ->
      let llist',arrlist' = walk llist arrlist t in
      List.fold_left (fun (l,al) (li,(xi,ti)) -> walk l al ti)
        (llist',arrlist') cases
  | TmLet(fi,x,t1,t2) ->
      let llist',arrlist' = walk llist arrlist t1 in
      walk llist' arrlist' t2
  | TmFix(fi,t1) -> walk llist arrlist t1
  | TmTimesfloat(fi,t1,t2) ->
      let llist',arrlist' = walk llist arrlist t1 in
      walk llist' arrlist' t2
  | TmIf(fi,t1,t2,t3) ->
      let llist',arrlist' = walk llist arrlist t1 in
      let llist',arrlist' = walk llist' arrlist' t2 in
      walk llist' arrlist' t3
  | TmProj(fi,t1,l) -> walk llist arrlist t1
  | TmRecord(fi,fields) ->
      List.fold_left (fun (l,al) (li,ti) -> walk l al ti) (llist,arrlist)
        fields
  | TmSucc(fi,t1)   -> walk llist arrlist t1
  | TmPred(fi,t1)   -> walk llist arrlist t1
  | TmIsZero(fi,t1) -> walk llist arrlist t1
  | TmArray(fi,tyT,t1,t2) ->
      let llist',arrlist' = walk llist arrlist t1 in
      walk llist' arrlist' t2
  | TmArrayIdx(fi,t1,t2) ->
      let llist',arrlist' = walk llist arrlist t1 in
      walk llist' arrlist' t2
  | _ -> llist, arrlist in
  let usedlocunordered, usedarrunordered = walk [] [] t in
  let usedloc = List.sort compare usedlocunordered in
  let usedarr = List.sort compare usedarrunordered in
  let rec newloc loclist n l = (match loclist with
    idx :: tail -> if l = idx then n else newloc loclist (n+1) l
  | _ -> raise NoRuleApplies) in
  let rec renumber t = match t with
    (* Actually we do not allow those variables in our implementation. *)
    TmVar(fi,x,n) as t -> t
  | TmAbs(fi,x,tyT1,t2) -> TmAbs(fi,x,tyT1,renumber t2)
  | TmApp(fi,t1,t2) -> TmApp(fi,renumber t1,renumber t2)
  | TmAscribe(fi,t1,tyT1) -> TmAscribe(fi,renumber t1,tyT1)
  | TmString _ as t -> t
  | TmUnit(fi) as t -> t
  | TmLoc(fi,l) -> TmLoc(fi, newloc usedloc 0 l)
  | TmArrayLoc(fi,a) -> TmArrayLoc(fi, newloc usedarr 0 a)
  | TmRef(fi,t1) -> TmRef(fi,renumber t1)
  | TmDeref(fi,t1) -> TmDeref(fi,renumber t1)
  | TmAssign(fi,t1,t2) -> TmAssign(fi,renumber t1,renumber t2)
  | TmTag(fi,l,t1,tyT) -> TmTag(fi, l, renumber t1, tyT)
  | TmCase(fi,t,cases) ->
      TmCase(fi, renumber t,
             List.map (fun (li,(xi,ti)) -> (li, (xi,renumber ti)))
               cases)
  | TmLet(fi,x,t1,t2) -> TmLet(fi,x,renumber t1,renumber t2)
  | TmFix(fi,t1) -> TmFix(fi,renumber t1)
  | TmFloat _ as t -> t
  | TmTimesfloat(fi,t1,t2) -> TmTimesfloat(fi, renumber t1, renumber t2)
  | TmError(_) as t -> t
  | TmTrue(fi) as t -> t
  | TmFalse(fi) as t -> t
  | TmIf(fi,t1,t2,t3) -> TmIf(fi,renumber t1,renumber t2,renumber t3)
  | TmProj(fi,t1,l) -> TmProj(fi,renumber t1,l)
  | TmRecord(fi,fields) -> TmRecord(fi,List.map (fun (li,ti) ->
                                               (li,renumber ti))
                                    fields)
  | TmZero(fi)      -> TmZero(fi)
  | TmSucc(fi,t1)   -> TmSucc(fi, renumber t1)
  | TmPred(fi,t1)   -> TmPred(fi, renumber t1)
  | TmIsZero(fi,t1) -> TmIsZero(fi, renumber t1)
  | TmInert(fi,tyT) -> TmInert(fi,tyT)
  | TmArray(fi,tyT,t1,t2) -> TmArray(fi, tyT, renumber t1, renumber t2)
  | TmArrayIdx(fi,t1,t2) -> TmArrayIdx(fi, renumber t1, renumber t2) in
  let t' = renumber t in
  let rec renumberstore store loclist n = match store with
    t :: sttail -> (match loclist with
        idx :: loctail -> if n = idx then
          (renumber t) :: (renumberstore sttail loctail (n+1))
        else renumberstore sttail loclist (n+1)
      | _ -> [])
  | _ -> [] in
  let store' = renumberstore store usedloc 0 in
  let rec renumlist l = match l with
    t :: tail -> (newloc usedloc 0 t) :: (renumlist tail)
  | _ -> [] in
  let rec renumberarrstore arrstore arrloclist n = match arrstore with
    arr :: arrtail -> (match arrloclist with
      idx :: loctail -> if n = idx then
        (renumlist arr) :: (renumberarrstore arrtail loctail (n+1))
        else renumberarrstore arrtail arrloclist (n+1)
      | _ -> [])
  | _ -> [] in
  let arrstore' = renumberarrstore arrstore usedarr 0 in
  t', store', arrstore'

let rec gceval ctx store arrstore t =
  try let t',store',arrstore' = eval1 ctx store arrstore t in
    let t'',store'',arrstore'' = gceval1 ctx store' arrstore' t' in
    eval ctx store'' arrstore'' t''
  with NoRuleApplies -> t,store,arrstore