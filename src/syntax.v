(* From Arthur's "pretty big-step semantics"
   http://www.chargueraud.org/research/2012/pretty/ 

   Source: CoreCaml_Syntax.v
*)


Require Import ssreflect ssrbool eqtype seq.
Require Import var int heap env.

Set Implicit Arguments.

(** * Definitions *)

(** ** Auxiliary definitions for the syntax *)

(** Representation of record labels *)

Definition lab := var.

(** Representation of constructors *)

Definition constr := var.

(** Representation of meta-variables *)

Definition metavar := var.

(** Particular exceptions *)

Parameter constr_unit : constr.
Parameter constr_matching_failure : constr.

(** Representation of locations *)

Definition loc := var.

(** Grammar of primitive operators *)

Inductive prim : Type :=
  | prim_raise : prim
  | prim_eq : prim
  | prim_not : prim
  | prim_neg : prim
  | prim_add : prim
  | prim_sub : prim
  | prim_mul : prim
  | prim_and : prim
  | prim_or : prim.

(** Grammar of constants *)

Inductive cst : Type :=
  | cst_bool : bool -> cst
  | cst_int : int -> cst.

Definition cst_eq (x y: cst): bool :=
  match x, y with
    | cst_bool b1, cst_bool b2 => b1 == b2
    | cst_int n1, cst_int n2 => Zeq_bool n1 n2
    | _, _ => false
  end.

Lemma cst_eqK: Equality.axiom cst_eq.
Proof.
  move=> x y.
  case: x; case: y;
  try (intros; apply ReflectF; discriminate).
  {
    move=> b1 b2 //=.
    apply: (iffP idP).
    * move/eqP=> ->; done.
    * move=> [->]; done.
  }
  {
    move=> n1 n2 //=.
    apply: (iffP idP).
    * move=> H.
      rewrite (Zeq_bool_eq n2 n1) //=.
    * move=> [->].
      apply Zeq_is_eq_bool.
      done.
  }
Qed.
Definition cst_eqMixin := @Equality.Mixin cst cst_eq cst_eqK.
Canonical Structure cst_eqType := Eval hnf in EqType _ cst_eqMixin.


(** Grammar of patterns *)

Inductive pat : Type :=
  | pat_var : var -> pat
  | pat_wild : pat
  | pat_or : pat -> pat -> pat
  | pat_cst : cst -> pat
  | pat_constr : constr -> seq pat -> pat.

Fixpoint pat_eq (x y: pat) {struct x}: bool :=
  match x, y with
    | pat_var v1, pat_var v2 => v1 == v2
    | pat_wild, pat_wild => true
    | pat_or p1 p1', pat_or p2 p2' => pat_eq p1 p2 && pat_eq p1' p2'
    | pat_cst c1, pat_cst c2 => c1 == c2
    | pat_constr c1 ps1, pat_constr c2 ps2 =>
      (c1 == c2) &&
      ((fix all_pat_eq (xs: seq pat): seq pat -> bool :=
         (fun ys =>
            match xs, ys with
              | [::], [::] => true
              | x :: xs, y :: ys => (pat_eq x y) && (all_pat_eq xs ys)
              | _, _ => false
            end)) ps1 ps2)
    | _, _ => false
end.


Lemma pat_eqK: Equality.axiom pat_eq.
Proof.
  move=> x y.
  case: x; case: y;
    try (apply ReflectT; done);
    try (intros; apply ReflectF; discriminate);
    admit.
  (*
  move=> b1 b2.
  rewrite //=.
  apply: (iffP idP).
  * move/eqP=> ->; done.
  * move=> [->]; done.
*)
Qed.
Definition pat_eqMixin := @Equality.Mixin pat pat_eq pat_eqK.
Canonical Structure pat_eqType := Eval hnf in EqType _ pat_eqMixin.


(** Grammar of terms *)

Inductive trm : Type :=
  | trm_var : var -> trm
  | trm_metavar: metavar -> seq trm -> trm
  | trm_cst : cst -> trm
  | trm_abs : option var -> pat -> trm -> trm
  | trm_constr : constr -> seq trm -> trm
  | trm_unary : prim -> trm -> trm
  | trm_binary : prim -> trm -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : pat -> trm -> trm -> trm  
  | trm_if : trm -> trm -> option trm -> trm
  | trm_match : trm -> seq branch -> trm
with branch : Type := 
  | branch_intro : pat -> option trm -> trm -> branch.


Lemma trm_eq (x y: trm): { x = y } + { x <> y }.
decide equality; admit.
Qed.
Definition trm_eqMixin := Equality.Mixin  (compareP trm_eq).
Canonical Structure trm_eqType := Eval hnf in EqType _ trm_eqMixin.


(** Grammar of values *)

Inductive val : Type :=
  | val_cst : cst -> val
  | val_loc : loc -> val
  | val_abs : option var -> pat -> trm -> val
  | val_constr : constr -> seq val -> val.

Fixpoint val_eq (x y: val): bool :=
  match x, y with
    | val_cst c1, val_cst c2 => c1 == c2
    | val_loc l1, val_loc l2 => l1 == l2
    | val_abs v1 p1 t1, val_abs v2 p2 t2 => (v1 == v2) && (p1 == p2) && (t1 == t2)
    | val_constr c1 vs1, val_constr c2 vs2 =>
      (c1 == c2) &&
      ((fix seq_val_eq (xs : seq val) : seq val -> bool :=
          fun ys =>
            match xs, ys with
              | [::], [::] => true
              | x :: xs, y :: ys => (val_eq x y) && (seq_val_eq xs ys)
              | _, _ => false
            end) vs1 vs2)
    | _, _ => false
  end.

Lemma val_eqK: Equality.axiom val_eq.
Proof.
  move=> x y.
  case: x; case: y;
    try (apply ReflectT; done);
    try (intros; apply ReflectF; discriminate); admit.
Qed.
Definition val_eqMixin := @Equality.Mixin val val_eq val_eqK.
Canonical Structure val_eqType := Eval hnf in EqType _ val_eqMixin.


(** * Auxiliary definitions *)

(** Substitution *)

Definition inst := env val.

Parameter subst : forall (x:var) (v:val) (t:trm), trm.
Parameter substs : forall (i:inst) (t:trm), trm.

(** Shortnames for lists of terms and values *)

Definition trms := seq trm.
Definition vals := seq val.
Definition labtrms := seq (lab*trm).
Definition labvals := seq (lab*val).
Definition branches := seq branch.

(** Shortcuts for building terms and values *)

Definition val_exn (k: constr): val := val_constr k nil.

Definition val_unit := val_constr constr_unit nil.

(** Coercions *)

Coercion val_exn : constr >-> val.
Coercion cst_int : Z >-> cst.
Coercion cst_bool : bool >-> cst.
Coercion pat_var : var >-> pat.
Coercion val_loc : loc >-> val.
Coercion val_cst : cst >-> val.
Coercion trm_cst : cst >-> trm.

