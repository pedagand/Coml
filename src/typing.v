Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import var env syntax semantics.

(************************************************************)
(* ** Grammar of simple types *)

Definition tconstr := var.

Inductive typ :=
  | typ_bool : typ
  | typ_int : typ
  | typ_arrow : typ -> typ -> typ
  | typ_tconstr : tconstr -> list typ -> typ
.

Definition typ_eq (x y: typ): bool. admit. Qed.
Lemma typ_eqK: Equality.axiom typ_eq. Proof. admit. Qed.
Definition typ_eqMixin := @Equality.Mixin typ typ_eq typ_eqK.
Canonical Structure typ_eqType := Eval hnf in EqType _ typ_eqMixin.


Implicit Types S T : typ.

Notation INT := (typ_int).
Notation BOOL := (typ_bool).
Notation "T1 ⇒ T2" 
  := (typ_arrow T1 T2)
       (at level 60, right associativity).

(************************************************************)
(* ** Typing of constructors *)

Parameter constr_typing : constr -> list typ -> typ -> Prop.

Notation "⊢c C ∈  [ Ts ]⇒ T" 
  := (constr_typing C Ts T)
       (at level 80).

(************************************************************)
(* ** Typing of environments *)

Definition env := env.env typ.
Definition metas := env.env (seq typ * typ).

(************************************************************)
(* ** Typing of constants *)

Reserved Notation "⊢C c ∈ T" (at level 80).

Inductive cst_typing : cst -> typ -> Prop :=
| cst_typing_bool : forall b,

     (*——————————————————————–—–*)
        ⊢C cst_bool b ∈ BOOL

| cst_typing_int : forall n,

     (*——————————————————————–—–*)
        ⊢C cst_int n ∈ INT
where "⊢C c ∈ T" := (cst_typing c T).


(************************************************************)
(* ** Typing of primitives *)

Reserved Notation "⊢P p ∈ T" (at level 80).

Inductive prim_typing : prim -> typ -> Prop :=
| prim_typing_eq : forall T,

      (*—————————————————————————————————————————————————–—–*)
        ⊢P prim_eq ∈ T ⇒ T ⇒ BOOL

| prim_typing_not : 

      (*—————————————————————————————————————————————————–—–*)
        ⊢P prim_not ∈ BOOL ⇒ BOOL

| prim_typing_and : 

      (*—————————————————————————————————————————————————–—–*)
        ⊢P prim_and ∈ BOOL ⇒ BOOL ⇒ BOOL

| prim_typing_or : 

      (*—————————————————————————————————————————————————–—–*)
        ⊢P prim_or ∈ BOOL ⇒ BOOL ⇒ BOOL

| prim_typing_neg : 

      (*—————————————————————————————————————————————————–—–*)
        ⊢P prim_neg ∈ INT ⇒ INT

| prim_typing_add : 

      (*—————————————————————————————————————————————————–—–*)
        ⊢P prim_add ∈ INT ⇒ INT ⇒ INT

| prim_typing_sub : 

      (*—————————————————————————————————————————————————–—–*)      
        ⊢P prim_sub ∈ INT ⇒ INT ⇒ INT

| prim_typing_mul : 

      (*—————————————————————————————————————————————————–—–*)      
        ⊢P prim_mul ∈ INT ⇒ INT ⇒ INT

where "⊢P p ∈ T" := (prim_typing p T).


(************************************************************)
(* ** Typing of patterns *)

Reserved Notation "Γ ⊢p pat ∈ T" (at level 80).
Reserved Notation "Ω · Γ ⊢b b ∈ [ S ]⇒ T" (at level 80).
Reserved Notation "Ω · Γ ⊢ t ∈ T" (at level 80).

(* TODO: Use left-sided judgment for patterns *)

Inductive pat_typing : env -> pat -> typ -> Prop :=
| pat_typing_var : forall Γ x T, 

        binds x T Γ ->
     (*—————————————————————————————–*)
        Γ ⊢p pat_var x ∈ T

| pat_typing_wild : forall Γ T,

     (*—————————————————————————————–*)
        Γ ⊢p pat_wild ∈ T

| pat_typing_or : forall Γ p1 p2 T,

        Γ ⊢p p1 ∈ T ->
        Γ ⊢p p2 ∈ T ->
     (*—————————————————————————————–*)
        Γ ⊢p pat_or p1 p2 ∈ T

| pat_typing_cst : forall Γ c T,

        ⊢C c ∈ T ->
     (*—————————————————————————————–*)
        Γ ⊢p pat_cst c ∈ T 

| pat_typing_constr : forall Γ C ps Ts T,

        ⊢c C ∈ [ Ts ]⇒ T ->
        forall2 (fun p T => Γ ⊢p p ∈ T) ps Ts ->
     (*—————————————————————————————–*)
        Γ ⊢p pat_constr C ps ∈ T

(************************************************************)
(* ** Typing of terms *)

with trm_typing : metas -> env -> trm -> typ -> Prop := 
| trm_typing_var : forall Ω Γ x T,

(*        ok E -> *)
        binds x T Γ ->
      (*————————————————————————————————–*)
         Ω · Γ ⊢ trm_var x ∈ T

| trm_typing_metavar : forall Ω Γ m ts Ts T,

(*        ok E -> *)
        binds m (Ts, T) Ω ->
        forall2 (fun t T => Ω · Γ ⊢ t ∈ T) ts Ts ->
      (*————————————————————————————————–*)
         Ω · Γ ⊢ trm_metavar m ts ∈ T

| trm_typing_cst : forall Ω Γ c T,

(*        ok Γ ->  *)
        ⊢C c ∈ T ->
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_cst c ∈ T

| trm_typing_constr : forall Ω Γ C ts Ts T,

        ⊢c C ∈ [ Ts ]⇒ T ->
        forall2 (fun t T => Ω · Γ ⊢ t ∈ T) ts Ts ->
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_constr C ts ∈ T

| trm_typing_abs : forall Ω rec Γ Δ S T p t1,

        Δ ⊢p p ∈ S -> 
        Ω · Γ & Δ & rec ~~ (S ⇒ T) ⊢ t1 ∈ T -> 
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_abs rec p t1 ∈ S ⇒ T

| trm_typing_unary : forall Ω Γ prim s S T,

        ⊢P prim ∈ S ⇒ T ->
        Ω · Γ ⊢ s ∈ S ->
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_unary prim s ∈ T

| trm_typing_binary : forall Ω Γ prim s t S T U,

        ⊢P prim ∈ S ⇒ T ⇒ U ->
        Ω · Γ ⊢ s ∈ S ->
        Ω · Γ ⊢ t ∈ T ->
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_binary prim s t ∈ U

| trm_typing_app : forall Ω Γ S T f s,

        Ω · Γ ⊢ f ∈ S ⇒ T ->
        Ω · Γ ⊢ s ∈ S ->
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_app f s ∈ T

| trm_typing_seq : forall Ω Γ S T t1 t2,

        Ω · Γ ⊢ t1 ∈ S ->
        Ω · Γ ⊢ t2 ∈ T ->
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_seq t1 t2 ∈ T

| trm_typing_let : forall Ω Γ Δ S T p t1 t2,

        Δ ⊢p p ∈ S ->
        Ω · Γ ⊢ t1 ∈ S ->
        Ω · Γ & Δ ⊢ t2 ∈ T ->
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_let p t1 t2 ∈ T

| trm_typing_if : forall Ω Γ T c t1,

        Ω · Γ ⊢ c ∈ BOOL ->
        Ω · Γ ⊢ t1 ∈ T ->
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_if c t1 None ∈ T

| trm_typing_if2 : forall Ω Γ T c t1 t2,

        Ω · Γ ⊢ c ∈ BOOL ->
        Ω · Γ ⊢ t1 ∈ T ->
        Ω · Γ ⊢ t2 ∈ T ->
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_if c t1 (Some t2) ∈ T

| trm_typing_match : forall Ω Γ S T t (branches: seq branch),

        Ω · Γ ⊢ t ∈ S ->
        forall1 (fun branch => Ω · Γ ⊢b branch ∈ [ S ]⇒ T) branches ->
      (*————————————————————————————————–*)
        Ω · Γ ⊢ trm_match t branches ∈ T

with branch_typing : metas -> env -> typ -> branch -> typ -> Prop :=
  | branch_typing_intro : forall Ω Γ Δ S T p ot1 t2,

        Δ ⊢p p ∈ S ->
        (forall t1, ot1 = Some t1 ->
                    Ω · Γ & Δ ⊢ t1 ∈ BOOL) ->
        Ω · Γ & Δ ⊢ t2 ∈ T ->
      (*–———–———————————————————————————————–*)
        Ω · Γ ⊢b branch_intro p ot1 t2 ∈ [ S ]⇒ T

where "Γ ⊢p pat ∈ T" := (pat_typing Γ pat T)
and   "Ω · Γ ⊢ t ∈ T" := (trm_typing Ω Γ t T)
and   "Ω · Γ ⊢b b ∈ [ S ]⇒ T" := (branch_typing Ω Γ S b T).
