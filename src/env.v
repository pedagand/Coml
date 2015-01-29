(* From Arthur Chargueraud's TLC
   http://www.chargueraud.org/softs/tlc/ 

   Source: tlc/LibEnv.v
*)

Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import var.

Set Implicit Arguments.
Set Contextual Implicit. 

(* ********************************************************************** *)
(** * Definition of environments and their basic operations *)


Definition env (A:Type) := seq (var * A).


(** ** Operations *)

Section Operations.
Variable A B : Type.

Definition empty : env A := [::].
Definition single x v : env A := [:: (x,v) ].
Definition concat (E F : env A) := F ++ E.
Definition singles (xs : list var) (vs : list A) : env A := zip xs vs.
Definition keys (E : env A): seq var := [seq fst x | x <- E ].
Definition values (E : env A): seq A := [seq snd x | x <- E ].
Definition fold_vars (fv : A -> vars) (E : env A): vars :=
  foldr (fun v acc => fv v ++ acc) [::] (values E).
Definition map (f:A->B) (E:env A) := [seq (fst x, f (snd x)) | x <- E ].
Definition map_keys (f:var->var) (E:env A) := [seq (f (fst x), snd x) | x <- E].
Definition dom (E : env A): vars :=  keys E.
Fixpoint get (k : var) (E : env A) {struct E} : option A :=
  match E with
  | [::] => None
  | [:: (x,v) & E' ] => if k == x then Some v else get k E'
  end.

End Operations.


(** ** Notations *)

(** [x ~ a] is the notation for a singleton environment mapping x to a. *)

Notation "x ~ a" := (single x a)
  (at level 27, left associativity) : env_scope.

(** [xs ~* vs] is the notation for [single_iter xs vs]. *)

Notation "xs ~* vs" := (singles xs vs)
  (at level 27, left associativity) : env_scope.

(** [E & F] is the notation for concatenation of E and F. *)

Notation "E & F" := (concat E F) 
  (at level 28, left associativity) : env_scope.

(** [x # E] to be read x fresh from E captures the fact that 
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Bind Scope env_scope with env.
Delimit Scope env_scope with env.
Open Scope env_scope.


(** ** Additional definitions *)

Section MoreDefinitions.
  
Variable A : Type.
Implicit Types E F : env A.

(** An environment contains a binding from x to a iff the most recent
  binding on x is mapped to a *)

Definition binds x v E := 
  get x E = Some v.


End MoreDefinitions.

