Require Import ssreflect ssrbool eqtype seq.
Require Import var syntax env typing.

Definition NAT: typ := typ_tconstr 0 [::].

Definition pat_Z := pat_constr 0 [::].
Definition constr_Z := trm_constr 0 [::].
Parameter constr_typing_Z : ⊢c 0 ∈  [[::] ]⇒ NAT.

Definition pat_S p := pat_constr 1 [:: p].
Definition constr_S t := trm_constr 1 [:: t].
Parameter constr_typing_S : ⊢c 1 ∈  [[:: NAT] ]⇒ NAT.

Definition add: trm
  := trm_abs
       (Some 0) (pat_var 1)
       (trm_abs
          None (pat_var 2)
          (trm_match
             (trm_var 1)
             [:: branch_intro
                  pat_Z
                  None
                  (trm_var 2)
              ; branch_intro
                  (pat_S (pat_var 3))
                  None
                  (constr_S
                     (trm_app
                        (trm_app
                           (trm_var 0)
                           (trm_var 3))
                        (trm_var 2)))])).

Lemma typing_add: empty · empty ⊢ add ∈ NAT ⇒ NAT ⇒ NAT.
Proof.
  apply trm_typing_abs with (Δ := 1 ~ NAT);
    first by apply pat_typing_var=> //=.
  apply trm_typing_abs with (Δ := 2 ~ NAT);
    first by apply pat_typing_var=> //=.
  apply trm_typing_match with (S := NAT);
    first by apply trm_typing_var=> //=.
  repeat constructor.
  * apply branch_typing_intro with (Δ := [::]).
    - apply pat_typing_constr with (Ts := [::]);
        first by apply constr_typing_Z.
      by constructor.
    - by move=> t //.
    - by apply trm_typing_var=> //=.
  * apply branch_typing_intro with (Δ := 3 ~ NAT).
    - apply pat_typing_constr with (Ts := [:: NAT]);
        first by apply constr_typing_S.
      repeat constructor; by apply pat_typing_var=> //=.
    - by move=> t //.
    - apply trm_typing_constr with (Ts := [:: NAT]);
        first by apply constr_typing_S.
      repeat constructor.
      apply trm_typing_app with (S := NAT); 
        last by apply trm_typing_var=> //=.
      apply trm_typing_app with (S := NAT);
        last by apply trm_typing_var=> //=.
      apply trm_typing_var=> //=.
Qed.


Definition LISTBOOL: typ := typ_tconstr 1 [::].

Definition pat_Nil := pat_constr 2 [::].
Definition constr_Nil := trm_constr 2 [::].
Parameter constr_typing_Nil : ⊢c 2 ∈  [[::] ]⇒ LISTBOOL.

Definition pat_Cons pa ps := pat_constr 3 [:: pa ; ps].
Definition constr_Cons a t := trm_constr 3 [:: a ; t].
Parameter constr_typing_Cons : ⊢c 3 ∈  [[:: BOOL ; LISTBOOL] ]⇒ LISTBOOL.

Definition lifting_add: trm
  := trm_abs
       (Some 0) (pat_var 1)
       (trm_abs
          None (pat_var 2)
          (trm_match
             (trm_var 1)
             [:: branch_intro
                  pat_Nil
                  None
                  (trm_var 2)
              ; branch_intro
                  (pat_Cons (pat_var 4) (pat_var 3))
                  None
                  (constr_Cons 
                     (trm_metavar 0 [:: trm_var 4; trm_var 3; trm_var 2; trm_var 1; trm_var 0 ])
                     (trm_app
                        (trm_app
                           (trm_var 0)
                           (trm_var 3))
                        (trm_var 2)))])).


Lemma typing_lifting_add: 
  (0 ~ ([:: BOOL ; LISTBOOL ; LISTBOOL ; LISTBOOL ; LISTBOOL ⇒ LISTBOOL ⇒ LISTBOOL ] , BOOL)) · empty ⊢ lifting_add ∈ LISTBOOL ⇒ LISTBOOL ⇒ LISTBOOL.
Proof.
  apply trm_typing_abs with (Δ := 1 ~ LISTBOOL);
    first by apply pat_typing_var=> //=.
  apply trm_typing_abs with (Δ := 2 ~ LISTBOOL);
    first by apply pat_typing_var=> //=.
  apply trm_typing_match with (S := LISTBOOL);
    first by apply trm_typing_var=> //=.
  repeat constructor.
  * apply branch_typing_intro with (Δ := [::]).
    - apply pat_typing_constr with (Ts := [::]);
        first by apply constr_typing_Nil.
      by constructor.
    - by move=> t //.
    - by apply trm_typing_var=> //=.
  * apply branch_typing_intro with (Δ := 4 ~ BOOL & 3 ~ LISTBOOL).
    - apply pat_typing_constr with (Ts := [:: BOOL ; LISTBOOL]);
        first by apply constr_typing_Cons.
      by repeat constructor. 
    - by move=> t //.
    - apply trm_typing_constr with (Ts := [:: BOOL ; LISTBOOL]);
        first by apply constr_typing_Cons.
      repeat constructor.
      eapply trm_typing_metavar=> //=;
        by repeat constructor.
      apply trm_typing_app with (S := LISTBOOL); 
        last by apply trm_typing_var=> //=.
      apply trm_typing_app with (S := LISTBOOL);
        last by apply trm_typing_var=> //=.
      apply trm_typing_var=> //=.
Qed.



Definition admitted {X}: X. admit. Qed.

Definition lookup (Γ: env)(x: var)(T: typ): option (Γ ⊢ trm_var x ∈ T).
 refine ((match get x Γ
                as o'
                return (get x Γ = o' -> option (Γ ⊢ trm_var x ∈ T))
      with
        | None => (fun _ => None)
        | Some T' => 
          (match T == T' as b 
                return (T == T' = b -> get x Γ = Some T' -> option (Γ ⊢ trm_var x ∈ T)) with
            | false => (fun _ _ => None)
            | true => (fun q1 q2 => Some (trm_typing_var _ _ _ _))
           end) Logic.eq_refl
          end) Logic.eq_refl).
move/eqP: q1=> [->]; done.
Defined.

Fixpoint check (Γ: env)(t: trm)(T: typ) : option (Γ ⊢ t ∈ T) :=
  match t return option (Γ ⊢ t ∈ T) with
    | trm_var x => 
      lookup Γ x T
    | _ => None
  end.

Fixpoint lift {Γ t T} (d: Γ ⊢ t ∈ T): orn T -> trm
  := 

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



