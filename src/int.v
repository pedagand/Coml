(* From Arthur Chargueraud's TLC
   http://www.chargueraud.org/softs/tlc/

  Source: tlc/LibInt.v
 *)

Require Export ZArith. 

Set Implicit Arguments.  

(* ********************************************************************** *)
(** * Notation for integers *)

Open Scope Z_scope.

Notation "'int'" := Z : Int_scope.

Infix "+" := Zplus : Int_scope.
Notation "- x" := (Zopp x) : Int_scope.
Infix "-" := Zminus : Int_scope.
Infix "*" := Zmult : Int_scope.

Bind Scope Int_scope with Z.
Delimit Scope Int_scope with I.
Open Scope Int_scope.

