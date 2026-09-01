Require Import ssreflect ssrbool ssrfun.
From HB Require Import structures.
From mathcomp Require Import ssrnat eqtype zify choice generic_quotient.

(* Z-ify: to make a ring like the integers, i.e. to make it be usable with lia
(it also imports lia) *)

(* Luna attempt at making the free jonsson tarski algeba. the node operator is usually called 
lambda in the literature and the child operators are usually called alpha_0 alpha_1. dont know if 
we should imitate that or stick to this. (might matter if/when we change arity) *)

Inductive jt_expression :=
| JEmpty: jt_expression
| JNode: jt_expression -> jt_expression -> jt_expression
| JLeft: jt_expression -> jt_expression
| JRight: jt_expression -> jt_expression.

(*

   act: jt_expression -> Cantor -> Cantor

   act t gamma :=
   match t with
   | JEmpty => gamma
   | JNode tl tr =>
    if gamma starts with 0 then
      act tl gamma
    else
      act tr gamma
   | JLeft t' =>
     prepend 0 to (act t' gamma)
   | JRight t' =>
     prepend 1 to (act t' gamma)
   end.

   A reduced expression is
   Node (Node (Node ...) Node ...)
   and the leaves are
   words in T

*)

Scheme Equality for jt_expression.
(* In general, all mathcomp functions for naturals are suffixed with "n",
   so if something doesnt work with nats, try adding n. *)
(*Print max.*)
(*Print maxn.*)
(*Check lt: nat -> nat -> Prop.*)
(*Check ltn: nat -> nat -> bool.*)

Fixpoint jt_depth (t : jt_expression) : nat :=
  match t with
  | JEmpty => 0
  | JNode a b =>
      S (maxn (jt_depth a) (jt_depth b))
  | JLeft x =>
      S (jt_depth x)
  | JRight x =>
      S (jt_depth x)
  end.

Lemma depth_zero_is_empty (x : jt_expression):
  jt_depth x = 0 -> x = JEmpty.
Proof.
  (* tactic_name: variable_name 
     dropping variable name from the hypothesis into "the stack" 

     tactic_name => variable_name
     taking the variable from the stack into the hypotheses

     /= is the same as simpl, but you can use it after => in-between introducing
     vars

     // - try to close goal automatically (does some simplification under the
     hood)

     by some_sequence_of_steps - do some_sequence_of_steps and then try to
     close the goal.
  *)
  by case: x.
Qed.

(*Lemma depth_at_most_zero_is_empty (x : jt_expression):*)
(*  (jt_depth x <= 0) -> x = JEmpty.*)
(*Proof.*)
(*intro h.*)
(*have h1: jt_depth x = 0.*)
(*by lia.*)
(*exact: depth_zero_is_empty h1.*)
(*Qed.*)

(* Use Search when possible to find if goal is already proved *)
(* Search (?x <= ?x). *)

(*Lemma ref_leq: forall (n:nat), n<=n.*)
(*Proof.*)
(*by lia.*)
(*Qed.*)

(* Reflexivity *)
Lemma jt_expression_beq_refl : reflexive jt_expression_beq.
Proof.
  by elim => /= [|xl -> xr ->||].
Qed.

Print jt_expression_beq.


(* Symmetry *)
Lemma jt_expression_beq_sym : symmetric jt_expression_beq.
Proof.
  elim => [|xl Hl xr Hr|w Hw|w Hw]; case => //.
  move => yl yr /=.
  by rewrite Hl Hr.
Qed.


(* Transitivity *)
Lemma jt_expression_beq_trans : transitive jt_expression_beq.
Proof.
  elim => [|yl Hl yr Hr|w Hw|w Hw] x z; case: x; case: z => //.
  - by move => zl zr xl xr /= /andP [/Hl {}Hl /Hr {}Hr] /andP [/Hl -> /Hr ->].
  - by move => zl zr /Hw {}Hw /Hw.
  - by move => xl xr /Hw {}Hw /Hw.
Qed.

Fixpoint jt_reduce_exp (t : jt_expression) : jt_expression :=
  match t with
  | JEmpty => JEmpty
  | JNode a b => 
      match jt_reduce_exp a, jt_reduce_exp b with
      | JLeft x, JRight y => if (jt_expression_beq x y) then x else JNode (JLeft x) (JRight y)
      | x, y => JNode x y
      end
  | JLeft x =>
      match jt_reduce_exp x with
      | JNode a b => a
      | y => JLeft y
      end
  | JRight x =>
      match jt_reduce_exp x with
      | JNode a b => b
      | y => JRight y
      end
  end.

Lemma reducing_reduces_depth (t : jt_expression) : jt_depth (jt_reduce_exp t) <= jt_depth t.
Proof.
  elim: t => [//|xl Hl xr Hr|w Hw|w Hw] /=.
  - move: Hl Hr.
    case: (jt_reduce_exp xl); case: (jt_reduce_exp xr) => /=; try lia.
    move => yl yr.
    (* case: ifP does cases on the condition of first if ... then block. *)
    by case: ifP => /=; lia.
  - by move: Hw; case (jt_reduce_exp w) => /=; lia.
  - by move: Hw; case (jt_reduce_exp w) => /=; lia.
Qed.


(*Fixpoint is_reduced (x : jt_expression) : bool :=*)
(*  match x with*)
(*  | JEmpty => true*)
(*  | JLeft y =>*)
(*      match y with*)
(*      | JEmpty => true*)
(*      | JLeft z => is_reduced y*)
(*      | JRight z => is_reduced y*)
(*      | JNode z a => false*)
(*      end*)
(*  | JRight y =>*)
(*      match y with*)
(*      | JEmpty => true*)
(*      | JLeft z => is_reduced y*)
(*      | JRight z => is_reduced y*)
(*      | JNode z a => false*)
(*      end*)
(*  | JNode y z =>*)
(*      match y, z with*)
(*      | JLeft a, JRight b =>*)
(*          negb (jt_expression_beq a b) &&*)
(*          is_reduced y &&*)
(*          is_reduced z*)
(*      | _, _ => is_reduced y && is_reduced z*)
(*      end*)
(*  end.*)

Definition is_reduced (x: jt_expression): bool :=
  jt_expression_beq x (jt_reduce_exp x).

Lemma jt_expression_beqP: forall x y,
  reflect (x = y) (jt_expression_beq x y).
Proof.
  move => x y; apply (iffP idP) => [|->];
    last by apply jt_expression_beq_refl.
  elim: x y => [|xl Hl xr Hr|w Hw|w Hw]; case => //=.
  - by move => yl yr /andP [/Hl -> /Hr ->].
  - by move => y /Hw ->.
  - by move => x /Hw ->.
Qed.

Lemma depth_ind: forall (P: jt_expression -> Prop),
  (forall t, (forall t', jt_depth t' < jt_depth t -> P t') -> P t) ->
  forall t, P t.
Proof.
  move => P IH t.
  have: (exists n, jt_depth t = n); first by exists (jt_depth t).
  move => [n].
  elim/ltn_ind: n t => n IH' t Ht.
  apply IH; rewrite Ht => t' Ht'.
  by apply IH' with (jt_depth t').
Qed.

Lemma jt_reduction_is_idempotent:
  forall x, jt_reduce_exp (jt_reduce_exp x) = jt_reduce_exp x.
Proof.
  elim/depth_ind; case => [//|xl xr IH|w IH|w IH] /=.
  - have: (jt_reduce_exp (jt_reduce_exp xr)) = jt_reduce_exp xr;
      first by apply IH => /=; lia.
    have: (jt_reduce_exp (jt_reduce_exp xl)) = jt_reduce_exp xl;
    first by apply IH => /=; lia.
    case: (jt_reduce_exp xl) => [_ /= -> //|xll xlr|xlw|xlw].
      + by case: (jt_reduce_exp xr) =>
          [/= -> //|xrl xrr /= -> -> //|xrw /= -> -> //|xrw /= -> -> //].
      + case: (jt_reduce_exp xr) =>
          [/= -> //|xrl xrr /= -> -> //|xrw /= -> -> //|xrw].
        case: ifP => [/jt_expression_beqP -> /=|/= Hneq -> ->];
          last by rewrite Hneq.
        case Hrw: (jt_reduce_exp xrw) => [|xrwl xrwr|xrww|xrww].
        * by case.
        * move => Hrwl Hrwr; move: Hrw; rewrite Hrwl Hrwr => H.
          have: (jt_reduce_exp (jt_reduce_exp xrw) = jt_reduce_exp xrw).
            apply IH; admit.
          rewrite {1}H /= H jt_expression_beq_refl //.
        * by case.
        * by case.
      + case: (jt_reduce_exp xr) =>
        [/= -> //|xrl xrr /= -> -> //|xrw /= -> -> //|xrw /= -> -> //].
  - have: (jt_reduce_exp (jt_reduce_exp w)) = jt_reduce_exp w;
      first by apply IH => /=; lia.
      case: (jt_reduce_exp w) => [//|wl wr /=|ww /= -> //|ww /= -> //].
      case: (jt_reduce_exp wl) => [[] //|wll wlr [] //|wlw|wlw []//].
      case Hrw: (jt_reduce_exp wr) => [|wrl wrr|wrw|wrw].
        * by case.
        * by case.
        * by case.
        * case: ifP => [|_ [] //]. admit.
  - have: (jt_reduce_exp (jt_reduce_exp w)) = jt_reduce_exp w;
      first by apply IH => /=; lia.
      case: (jt_reduce_exp w) => [//|wl wr /=|ww /= -> //|ww /= -> //].
      case: (jt_reduce_exp wl) => [[] //|wll wlr [] //|wlw|wlw []//].
      case Hrw: (jt_reduce_exp wr) => [|wrl wrr|wrw|wrw].
        * by case.
        * by case.
        * by case.
        * case: ifP => [|_ [] //]. admit.
Admitted.
    


Definition jt_equiv : rel jt_expression :=
  fun x y => jt_expression_beq (jt_reduce_exp x) (jt_reduce_exp y).

(* Reflexivity *)
Lemma jt_equiv_refl : reflexive jt_equiv.
Proof.
  move=> x.
  exact : jt_expression_beq_refl (jt_reduce_exp x).
Qed.


(* Symmetry *)
Lemma jt_equiv_sym : symmetric jt_equiv.
Proof.
  move=> x y.
  exact : jt_expression_beq_sym (jt_reduce_exp x) (jt_reduce_exp y).
Qed.

(* Transitivity *)
Lemma jt_equiv_trans : transitive jt_equiv.
Proof.
  move=> x y z.
  exact : jt_expression_beq_trans (jt_reduce_exp x) (jt_reduce_exp y) (jt_reduce_exp z).
Qed.

Definition jt_equiv' := EquivRel jt_equiv jt_equiv_refl jt_equiv_sym jt_equiv_trans.


(* For operations, define 
   compositions of reduction + constructor
   and give nice notation if need be.
*)

(* For choice Type, try to
  write a function which takes a jt_expression and returns a
  GenTree.tree T, then a (partial) inverse function and then use
  pcan_type to get a countaqble structure on jt_expression type.

   Maybe this instead? PCanIsCountable ff'

https://math-comp.github.io/htmldoc/mathcomp.boot.choice.html


Alternatively we can try builidng it directly

isQuotient.Build T Q (reprK : cancel repr pi) == builds the quotient
             whose canonical surjection function is (pi : T -> Q) and
             whose representative selection function is repr

https://math-comp.github.io/htmldoc/mathcomp.boot.generic_quotient.html
 *)
