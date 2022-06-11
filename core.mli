(* module Core

   Core typechecking and evaluation functions
*)

open Syntax
open Support.Error

val typeof : context -> term -> ty
val subtype : context -> ty -> ty -> bool
type store
type arrstore
val emptystore : store
val emptyarrstore : arrstore
val shiftstore : int -> store -> store 
val eval : context -> store -> arrstore -> term -> term * store * arrstore
val evalbinding : context -> store -> arrstore -> binding -> binding * store * arrstore
val tyeqv : context -> ty -> ty -> bool
val simplifyty : context -> ty -> ty
