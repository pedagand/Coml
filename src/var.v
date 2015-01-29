(* From Arthur Chargueraud's TLC
   http://www.chargueraud.org/softs/tlc/ 

   Source: tlc/LibVar.v
*)

Require Import ssreflect ssrbool ssrnat eqtype seq.

Set Implicit Arguments.


(** * Concrete Implementation of Variables *)

Definition var := nat.
Definition vars := seq var.

Canonical var_eqType := Eval hnf in [eqType of nat].
Canonical vars_eqType := Eval hnf in [eqType of seq nat].


Implicit Types x: var.
Implicit Types l: vars.

Definition var_gen l := 1 + foldr addn 0 l.

Lemma var_gen_spec :
  forall x l,
    x \in l -> x < var_gen l.
Proof.
  (* PE: *) admit.
    (*
    move=> n l q.
    elim: l q=> //= [v l IH q].
    rewrite /(var_gen_list (_ :: _)) /=.
    *)
    (*
    unfold var_gen_list. induction l; introv I.
  rewrite from_list_nil in I. false (in_empty_elim I).
  rewrite from_list_cons in I. rew_list.
   rewrite in_union in I. destruct I as [H|H].
     rewrite in_singleton in H. subst. nat_math.
     specializes IHl H. nat_math.
     *)
Qed.

Lemma var_fresh : forall (l : vars), { x : var | x \notin l }.
Proof.
  (* PE: *)
  admit.
    (*
    intros L. exists (var_gen L). apply var_gen_spec. *)
Qed.

