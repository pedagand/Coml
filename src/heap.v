(* From Arthur Chargueraud's TLC
   http://www.chargueraud.org/softs/tlc/ 

   Source: tlc/LibHeap.v
*)

Require Import ssreflect eqtype choice ssrbool seq.

Set Implicit Arguments.

(** * Heaps: finite maps from keys to values *)

Section HeapDef.
  
  Variable K: eqType.
  Variable V: eqType.

  Definition heap K V := seq (K*V).
  Canonical heap_eqType := Eval hnf in [eqType of heap K V].

  Definition empty : heap K V := [::].
  Definition dom (l : heap K V) : seq K := [seq fst x | x <- l ].
  Definition binds (l : heap K V) k v := (k,v) \in l.
  Definition to_list (l : heap K V) := l.
  Definition read (l : heap K V)(k : K) := ohead [seq kv <- l | fst kv == k ].
  Definition write (l : heap K V) k v := [:: (k, v) & l].
  Definition rem (l : heap K V) k := [seq p <- l | ~~ (fst p == k) ].
  Definition indom h r := (r \in dom h).

End HeapDef.

Arguments empty [K V].
Arguments dom [K V] h : rename.
Arguments binds [K V] h k v : rename.
Arguments read [K V] h k : rename.
Arguments write [K V] h k v : rename.
Arguments to_list [K V] h : rename.
Arguments indom [K V] h r : rename.


