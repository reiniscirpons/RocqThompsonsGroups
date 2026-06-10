Require Import ssreflect ssrbool ssrfun.
From HB Require Import structures.


(* Luna attempt at making the free jonsson tarski algeba. the node operator is usually called 
lambda in the literature and the child operators are usually called alpha_0 alpha_1. dont know if 
we should imitate that or stick to this. (might matter if/when we change arity) *)

Inductive jt_expression :=
| JEmpty: jt_expression
| JNode: jt_expression -> jt_expression -> jt_expression
| JLeft: jt_expression -> jt_expression
| JRight: jt_expression -> jt_expression.

Scheme Equality for jt_expression.


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

Definition is_reduced_jt (t : jt_expression) : Prop :=
  jt_reduce_exp t = t.

Lemma jt_reduction_is_idempotent (t : jt_expression) : is_reduced_jt (jt_reduce_exp t).
Proof.
unfold is_reduced_jt.
induction t.
unfold jt_reduce_exp.
reflexivity.
Admitted.

Record jt := {
  normal_form :> jt_expression;
  is_normal_form : is_reduced_jt normal_form;
}.

Definition JTNode (l r : jt) : jt :=
  {| normal_form :=
       jt_reduce_exp (JNode (normal_form l) (normal_form r));
     is_normal_form :=
       jt_reduction_is_idempotent (JNode (normal_form l) (normal_form r));
  |}.


Definition JTLeft (n : jt) : jt :=
  {| normal_form :=
       jt_reduce_exp (JLeft (normal_form n));
     is_normal_form :=
       jt_reduction_is_idempotent (JLeft (normal_form n));
  |}.

Definition JTRight (n : jt) : jt :=
  {| normal_form :=
       jt_reduce_exp (JRight (normal_form n));
     is_normal_form :=
       jt_reduction_is_idempotent (JRight (normal_form n));
  |}.

Definition JTeq (x : jt) (y : jt) : bool := jt_expression_beq (normal_form x) (normal_form y).
