(* From Arthur's "pretty big-step semantics"
   http://www.chargueraud.org/research/2012/pretty/ 

   Source: CoreCaml_Pretty.v
*)


Require Import ssreflect ssrbool eqtype seq.
Require Import var int env heap syntax.

Set Implicit Arguments.

Implicit Types x : var.
Implicit Types c : cst.
Implicit Types f : prim.
Implicit Types k : constr.
Implicit Types v : val.
Implicit Types t : trm.
Implicit Types a : lab.
Implicit Types l : loc.
Implicit Types i : inst.
Implicit Types n : int.
Implicit Types z : bool.

(** * Definitions *)

(** ** Auxiliary definitions *)

(** Grammar of behaviors *)

Inductive beh :=
  | beh_ret : val -> beh
  | beh_exn : val -> beh.

Coercion beh_ret : val >-> beh.

(** Grammar of outcomes *)

Inductive out :=
  | out_ter : beh -> out.

Implicit Types o : out.

(** Grammar of extended terms *)

Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_unary_1 : prim -> out -> ext
  | ext_binary_1 : prim -> out -> trm -> ext
  | ext_binary_2 : prim -> val -> out -> ext
  | ext_app_1 : out -> trm -> ext
  | ext_app_2 : val -> out -> ext
  | ext_seq_1 : out -> trm -> ext
  | ext_let_1 : pat -> out -> trm -> ext         
  | ext_if_1 : out -> trm -> option trm -> ext
  | ext_match_1 : out -> branches -> ext 
  | ext_build_1 : (vals -> val) -> vals -> ext
  | ext_list_1 : trms -> vals -> (vals -> ext) -> ext
  | ext_list_2 : out -> trms -> vals -> (vals -> ext) -> ext
  | ext_branches_1 : beh -> val -> branches -> ext 
  | ext_branches_2 : beh -> val -> branches -> out -> trm -> ext.

Coercion ext_trm : trm >-> ext.
Implicit Types e : ext.

(** Outcomes in intermediate forms *)

Definition out_of_ext e :=
  match e with
  | ext_unary_1 _ o => Some o
  | ext_binary_1 _ o _ => Some o
  | ext_binary_2 _ _ o => Some o
  | ext_app_1 o _ => Some o
  | ext_app_2 _ o  => Some o
  | ext_seq_1 o _  => Some o
  | ext_let_1 _ o _ => Some o   
  | ext_if_1 o _ _ => Some o
  | ext_match_1 o _  => Some o
  | ext_list_2 o _ _ _ => Some o
  | ext_branches_2 _ _ _ o _ => Some o
  | _ => None
  end.
(*
  | ext_record_1 _ => None
  | ext_list_1 _ _ _ _ => None
  | ext_lablist_1 _ _ _ _ => None
  | ext_for_3 _ _ _ _ _ => None
  ext_branches_1
*)


(** ** Auxiliary semantics definitions *)

(** Semantics of Pattern matching *)

Inductive forall2 {A B} (P: A -> B -> Prop) : seq A -> seq B -> Prop :=
| Nil: forall2 P [::] [::]
| Cons : forall (x: A) xs y ys,
           P x y -> forall2 P xs ys -> forall2 P (x :: xs) (y :: ys).

Inductive matching (i : inst) : val -> pat -> Prop :=
  | matching_var : forall x v,
      env.binds x v i ->
      matching i v (pat_var x)
  | matching_wild : forall v,
      matching i v pat_wild
  | matching_or : forall v p p1 p2,
      matching i v p ->
      (p = p1 \/ p = p2) ->
      matching i v (pat_or p1 p2) 
  | matching_cst : forall c,
      matching i c (pat_cst c)
  | matching_constr : forall k vs ps,
      forall2 (matching i) vs ps ->
      matching i (val_constr k vs) (pat_constr k ps).

Definition mismatching v p := 
  forall i, ~ matching i v p.

(** Semantics of primitive equality *)

Parameter primitive_eq : val -> val -> bool -> Prop.


(************************************************************)
(** ** Evaluation of primitive functions *)

Inductive unary_pure : prim -> val -> beh -> Prop :=
  | unary_pure_neg : forall z,
      unary_pure prim_neg z (~~ z)
  | unary_pure_not : forall n,
      unary_pure prim_not n (-n).

Inductive unary_red : prim -> val -> out -> Prop :=
  | unary_red_pure : forall f v (b:beh),
      unary_pure f v b ->
      unary_red f v (out_ter b).

Inductive binary_pure : prim -> val -> val -> beh -> Prop :=
  | binary_pure_eq : forall v1 v2 z,
      primitive_eq v1 v2 z ->
      binary_pure prim_eq v1 v2 z
  | binary_pure_add : forall n1 n2,
      binary_pure prim_add n1 n2 (n1+n2) 
  | binary_pure_sub : forall n1 n2,
      binary_pure prim_sub n1 n2 (n1-n2) 
  | binary_pure_mul : forall n1 n2,
      binary_pure prim_mul n1 n2 (n1*n2).

Inductive binary_red : prim -> val -> val -> out -> Prop :=
  | binary_red_pure : forall f v1 v2 (b:beh),
      binary_pure f v1 v2 b ->
      binary_red f v1 v2 (out_ter b).


(************************************************************)
(** ** Evaluation judgment *)

Inductive red : ext -> out -> Prop :=
  | red_cst : forall c,
      red (trm_cst c) (out_ter c)
  | red_abs : forall oy p t,
      red (trm_abs oy p t) (out_ter (val_abs oy p t))
  | red_constr : forall k ts o,
      red (ext_list_1 ts nil (ext_build_1 (val_constr k))) o ->
      red (trm_constr k ts) o
  | red_unary : forall o1 f t1 o,
      red t1 o1 ->
      red (ext_unary_1 f o1) o ->
      red (trm_unary f t1) o
  | red_unary_1 : forall f v o,
      unary_red f v o ->
      red (ext_unary_1 f (out_ter v)) o
  | red_binary : forall o1 f t1 t2 o,
      red t1 o1 ->
      red (ext_binary_1 f o1 t2) o ->
      red (trm_binary f t1 t2) o
  | red_binary_1 : forall f v1 t2 o2 o,
      red t2 o2 ->
      red (ext_binary_2 f v1 o2) o ->
      red (ext_binary_1 f (out_ter v1) t2) o
  | red_binary_2 : forall f v1 v2 o,
      binary_red f v1 v2 o ->
      red (ext_binary_2 f v1 (out_ter v2)) o

  | red_app : forall t1 t2 o1 o,
      red t1 o1 ->
      red (ext_app_1 o1 t2) o ->
      red (trm_app t1 t2) o
  | red_app_1 : forall v1 t2 o2 o,
      red t2 o2 ->
      red (ext_app_2 v1 o2) o ->
      red (ext_app_1 (out_ter v1) t2) o
  | red_app_2_mismatch : forall oy p t3 v2,
      mismatching v2 p ->
      red (ext_app_2 (val_abs oy p t3) (out_ter v2))
             (out_ter (beh_exn constr_matching_failure))
  | red_app_2_match : forall oy p i t4 t5 t3 v2 o,
      matching i v2 p ->
      t4 = substs i t3 ->
      t5 = match oy with 
         | None => t4
         | Some y => (subst y (val_abs oy p t3) t4) end ->
      red t5 o ->
      red (ext_app_2 (val_abs oy p t3) (out_ter v2)) o

  | red_seq : forall t1 t2 o1 o,
      red t1 o1 ->
      red (ext_seq_1 o1 t2) o ->
      red (trm_seq t1 t2) o
  | red_seq_1 : forall v1 t2 o,
      red t2 o ->
      red (ext_seq_1 (out_ter v1) t2) o
  | red_let : forall p t1 t2 o1 o,
      red t1 o1 ->
      red (ext_let_1 p o1 t2) o ->
      red (trm_let p t1 t2) o
  | red_let_1_match : forall i p v1 t2 o,
      matching i v1 p ->
      red (substs i t2) o ->
      red (ext_let_1 p (out_ter v1) t2) o
  | red_let_1_mismatch : forall p v1 t2,
      mismatching v1 p ->
      red (ext_let_1 p (out_ter v1) t2) 
             (out_ter (beh_exn constr_matching_failure))
  | red_if : forall t1 t2 ot3 o1 o,
      red t1 o1 ->
      red (ext_if_1 o1 t2 ot3) o ->
      red (trm_if t1 t2 ot3) o
  | red_if_1_true : forall t2 ot3 o,
      red t2 o ->
      red (ext_if_1 (out_ter true) t2 ot3) o
  | red_if_1_false_none : forall t2,
      red (ext_if_1 (out_ter false) t2 None) 
             (out_ter val_unit)
  | red_if_1_false_some : forall t2 t3 o,
      red t3 o ->
      red (ext_if_1 (out_ter false) t2 (Some t3)) o

  | red_match : forall t1 bs o1 o,
      red t1 o1 ->
      red (ext_match_1 o1 bs) o ->
      red (trm_match t1 bs) o
  | red_match_1 : forall v bs o,
      red (ext_branches_1 (beh_exn constr_matching_failure) v bs) o ->
      red (ext_match_1 (out_ter v) bs) o

  | red_build_1 : forall F vs,
      red (ext_build_1 F vs) (out_ter (F vs))
  | red_list_1_nil : forall K vs o,
      red (K vs) o ->
      red (ext_list_1 nil vs K) o
  | red_list_1_cons : forall K t1 ts o1 vs o,
      red t1 o1 ->
      red (ext_list_2 o1 ts vs K) o ->
      red (ext_list_1 (t1::ts) vs K) o
  | red_list_2 : forall K v1 ts vs o,
      red (ext_list_1 ts (vs++v1::nil) K) o ->
      red (ext_list_2 (out_ter v1) ts vs K) o

  | red_branches_1_nil : forall B v,
      red (ext_branches_1 B v nil)
            (out_ter B)
  | red_branches_1_cons_mismatch : forall p ot1 t2 B v bs o,
      mismatching v p ->
      red (ext_branches_1 B v bs) o ->
      red (ext_branches_1 B v ((branch_intro p ot1 t2)::bs)) o
  | red_branches_1_cons_match_unguarded : forall i p t2 B v bs o,
      matching i v p ->
      red (substs i t2) o ->
      red (ext_branches_1 B v ((branch_intro p None t2)::bs)) o
  | red_branches_1_cons_match_guarded : forall i p t1 o1 t2 B v bs o,
      matching i v p ->
      red (substs i t1) o1 ->
      red (ext_branches_2 B v bs o1 (substs i t2)) o ->
      red (ext_branches_1 B v ((branch_intro p (Some t1) t2)::bs)) o
  | red_branches_2_true : forall t B v bs o,
      red t o ->
      red (ext_branches_2 B v bs (out_ter true) t) o
  | red_branches_2_false : forall B t v bs o,
      red (ext_branches_1 B v bs) o ->
      red (ext_branches_2 B v bs (out_ter false) t) o.
      

