Require Import ssreflect ssrbool ssrfun.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat zify choice quotient generic_quotient seq.
Open Scope quotient_scope.
Require Import FunctionalExtensionality.

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

Scheme Equality for jt_expression.


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

Lemma depth_at_most_zero_is_empty (x : jt_expression):
  (jt_depth x <= 0) -> x = JEmpty.
Proof.
  case x.
  all: try by [].
Qed.

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

Check Equality.Mixin.
Lemma jt_expression_beq_axiom :
  Equality.axiom jt_expression_beq.
Proof.
  move=> x y.
  case: (jt_expression_eq_dec x y) => [->|H].
  - exact: jt_expression_beqP.
  - exact: jt_expression_beqP.
Qed.
Definition jt_expression_eqMixin : Equality.mixin_of jt_expression :=
  Equality.Mixin jt_expression_beq_axiom.

Definition jt_expression_eqType : eqType :=
  Equality.Pack (Equality.Class jt_expression_eqMixin).


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

Definition is_reduced (x: jt_expression): bool :=
  jt_expression_beq x (jt_reduce_exp x).


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
    

Lemma jt_reduction_is_reduced:
  forall x, is_reduced (jt_reduce_exp x).
Proof.
intro x; apply/jt_expression_beqP; by rewrite (jt_reduction_is_idempotent x).
Qed.

Lemma jt_reduce_of_reduced :
  forall x, is_reduced x = true -> jt_reduce_exp x = x.
Proof.
move => x hx; apply/ jt_expression_beqP; rewrite (jt_expression_beq_sym (jt_reduce_exp x) x) //.
Qed.

Definition jt_equiv' : rel jt_expression :=
  fun x y => jt_expression_beq (jt_reduce_exp x) (jt_reduce_exp y).
(* Reflexivity *)
Lemma jt_equiv'_refl : reflexive jt_equiv'.
Proof.
  move=> x.
  exact : jt_expression_beq_refl (jt_reduce_exp x).
Qed.
(* Symmetry *)
Lemma jt_equiv'_sym : symmetric jt_equiv'.
Proof.
  move=> x y.
  exact : jt_expression_beq_sym (jt_reduce_exp x) (jt_reduce_exp y).
Qed.
(* Transitivity *)
Lemma jt_equiv'_trans : transitive jt_equiv'.
Proof.
  move=> x y z.
  exact : jt_expression_beq_trans (jt_reduce_exp x) (jt_reduce_exp y) (jt_reduce_exp z).
Qed.
Definition jt_equiv := EquivRel jt_equiv' jt_equiv'_refl jt_equiv'_sym jt_equiv'_trans.
Definition jt_reduced_elt := { x : jt_expression | is_reduced x = true }.
Definition jt_pi (x : jt_expression) : jt_reduced_elt :=
   exist  is_reduced (jt_reduce_exp x) (jt_reduction_is_reduced x).
Definition jt_repr (q : jt_reduced_elt) : jt_expression := sval q.
Lemma jt_reprK : cancel jt_repr jt_pi.
Proof.
  move=> q; apply: val_inj.
  rewrite /jt_repr /jt_pi.
  exact: (jt_reduce_of_reduced (sval q) (proj2_sig q)).
Qed.
Fixpoint jt_encode (x : jt_expression) : GenTree.tree unit :=
  match x with
  | JEmpty => GenTree.Leaf tt
  | JNode x y => GenTree.Node 0 (cons (jt_encode x) (cons (jt_encode y) [::]))
  | JLeft x => GenTree.Node 1 [:: jt_encode x]
  | JRight x => GenTree.Node 2 [:: jt_encode x]
  end.
Fixpoint jt_decode (t : GenTree.tree unit) : option jt_expression :=
  match t with
  | GenTree.Leaf _ => Some JEmpty
  | GenTree.Node 0 [:: x; y] =>
      if jt_decode x is Some x' then
        if jt_decode y is Some y' then
          Some (JNode x' y')
        else None
      else None
  | GenTree.Node 1 [:: x] =>
      if jt_decode x is Some x' then
        Some (JLeft x')
      else None
  | GenTree.Node 2 [:: x] =>
      if jt_decode x is Some x' then
        Some (JRight x')
      else None
  | _ => None
  end.
Lemma jt_decodeK : pcancel jt_encode jt_decode.
Proof.
  elim => [|x IHx y IHy|x IHx|x IHx] /=.
  - by [].
  - by rewrite IHx IHy.
  - by rewrite IHx.
  - by rewrite IHx.
Qed.
Definition jt_decode' (t : GenTree.tree unit) : jt_expression :=
  odflt JEmpty (jt_decode t).
Lemma jt_decodeK' :
  forall x : jt_expression,
    jt_decode' (jt_encode x) = x.
Proof.
  move=> x.
  rewrite /jt_decode'.
  move: (jt_decodeK x).
  case: (jt_decode (jt_encode x)) => [y|] //=.
  move=> H.
  by inversion H.
Qed.
Lemma jt_enc_condition :
  forall x : jt_expression,
    jt_equiv' x x ->
    jt_equiv' (jt_decode' (jt_encode x)) x.
Proof.
  move=> x _.
  rewrite (jt_decodeK' x).
  exact: jt_equiv'_refl.
Qed.
Definition jt_encModRel :
  encModRel jt_decode' jt_encode jt_equiv :=
  @EncModRelPack
    jt_expression
    (GenTree.tree unit)
    jt_decode'
    jt_encode
    jt_equiv
    jt_equiv'
    (EncModRelClassPack
      jt_enc_condition
      (fun x y => erefl)).
Definition jt_expression_choiceType :=
  Choice.Pack
    (Choice.Class
      (HB_unnamed_factory_6 jt_decodeK)
      (eqtype.HB_unnamed_mixin_14 jt_decodeK)).
Canonical jt_expression_choiceType.
Definition jt_elt := {eq_quot jt_encModRel}.
Definition jt_proj : jt_expression -> jt_elt :=
  @pi jt_expression jt_elt.
Definition jt_rep_temp (q : jt_elt) : jt_expression :=
  jt_decode' (EquivQuot.erepr q).
Lemma jt_proj_rep_temp_cancel (x: jt_elt): jt_proj (jt_rep_temp x) = x.
Proof.
rewrite /jt_proj /jt_rep_temp.
  rewrite pi.unlock.
  exact: (EquivQuot.equivQTP (encD := jt_encModRel) x).
Qed.
Lemma jt_proj_ker (x y: jt_expression): 
jt_proj x = jt_proj y <-> jt_equiv x y.
Proof.
split.
- move=> h.
  apply/(EquivQuot.eqmodP jt_encModRel).
  exact: h.
- move=> h.
  apply: (EquivQuot.eqmodP jt_encModRel).
  exact: h.
Qed.
Definition jt_rep (q : jt_elt) : jt_expression :=
  jt_reduce_exp (jt_rep_temp q).
Lemma jt_proj_rep_cancel (x: jt_elt): jt_proj (jt_rep x) = x.
Proof.
have Ht: jt_equiv (jt_rep x) (jt_rep_temp x).
- simpl; apply /jt_expression_beqP. 
  apply /jt_expression_beqP; rewrite jt_expression_beq_sym.
  exact: jt_reduction_is_reduced (jt_rep_temp x).
rewrite ((jt_proj_ker (jt_reduce_exp (jt_rep_temp x)) (jt_rep_temp x)).2 Ht).
exact: jt_proj_rep_temp_cancel x.
Qed.
Lemma jt_rep_proj_cancel (x: jt_expression): jt_rep (jt_proj x) = jt_reduce_exp x.
Proof.
apply /jt_expression_beqP; exact ((jt_proj_ker (jt_rep_temp (jt_proj x)) x).1 (jt_proj_rep_temp_cancel (jt_proj x))).
Qed.
Lemma jt_rep_proj_cancel_mod (x: jt_expression): jt_equiv (jt_rep (jt_proj x)) x.
- rewrite jt_rep_proj_cancel.
  unfold jt_equiv. simpl. unfold jt_equiv'.
  apply/ jt_expression_beqP.
  exact (jt_reduction_is_idempotent x).
Qed.

Definition quotient_pass_func (f: jt_expression-> jt_expression): jt_elt -> jt_elt :=
 (fun x => jt_proj (f (jt_rep x))).
Definition quotient_pass_2func
  (f : jt_expression -> jt_expression -> jt_expression)
  : jt_elt -> jt_elt -> jt_elt :=
  (fun x y => jt_proj (f (jt_rep x) (jt_rep y))).

Definition jt_gen : jt_elt := jt_proj JEmpty.
Definition jt_alpha_0 : jt_elt -> jt_elt := 
quotient_pass_func (fun x => JLeft x).
Definition jt_alpha_1 : jt_elt -> jt_elt := 
quotient_pass_func (fun x => JRight x).
Definition jt_lambda : jt_elt -> jt_elt -> jt_elt := 
quotient_pass_2func (fun x y => JNode x y).
Definition is_jt_endo: (jt_elt -> jt_elt) -> Prop := 
fun f => 
(forall x : jt_elt, f (jt_alpha_0 x) = jt_alpha_0 (f x)) /\
(forall x : jt_elt, f (jt_alpha_1 x) = jt_alpha_1 (f x)) /\
(forall x y : jt_elt, f (jt_lambda x y) = jt_lambda (f x) (f y)).

Definition TV : Type := { f : (jt_elt -> jt_elt) | is_jt_endo f }.
Definition TV_act: TV -> jt_elt -> jt_elt := fun f x => (proj1_sig f) x.
Definition TV_eq (f g : TV) : Prop := proj1_sig f = proj1_sig g.
Lemma TV_is_magma: forall (f g : TV), is_jt_endo (fun x => (proj1_sig f) ((proj1_sig g) x)).
Proof.
move => f g; case: f => f Hf; case: g => g Hg.
simpl.
split.
2: split.
all: intro x; try intro y.
rewrite (Hg.1 x).
by rewrite (Hf.1 (g x)).
rewrite (Hg.2.1 x).
by rewrite (Hf.2.1 (g x)).
rewrite (Hg.2.2 x).
by rewrite (Hf.2.2 (g x)).
Qed.
Definition TV_comp : TV -> TV -> TV :=
  fun f g =>
    exist _
      (fun x => (proj1_sig f) ((proj1_sig g) x))
      (TV_is_magma f g).
Lemma TV_is_semigroup: forall (f g h: TV), 
TV_eq (TV_comp (TV_comp h g) f) (TV_comp h (TV_comp g f)).
Proof.
by [].
Qed.
Lemma TV_action_associates: forall (f g: TV) (x:jt_elt), 
TV_act (TV_comp f g) x = TV_act f (TV_act g x).
Proof.
by [].
Qed.
Lemma TV_action_determined: forall (f g: TV), (forall (x:jt_elt), 
TV_act f x = TV_act g x) -> TV_eq f g.
Proof.
move => f g hype.
unfold TV_eq.
apply (@functional_extensionality_dep jt_elt (fun _ => jt_elt)).
by unfold TV_act in hype.
Qed.
Definition TV_eq_determines_action (f g : TV): forall (x:jt_elt), TV_eq f g -> TV_act f x = TV_act g x.
Proof.
move => x heq.
unfold TV_eq in heq.
unfold TV_act. by rewrite heq.
Qed.

Lemma jt_elt_rec :
  forall (P : jt_elt -> Type),
    P jt_gen
    -> (forall t, P t -> P (jt_alpha_0 t))
    -> (forall t, P t -> P (jt_alpha_1 t))
    -> (forall s t, P s -> P t -> P (jt_lambda s t))
    -> forall t, P t.
Proof.
  move => P Hg Ha0 Ha1 Hl.
  have goal : forall x : jt_expression, P (jt_proj x).
  - elim => [|xm hxm xf hxf|xl hxl|xr hxr].
    - exact: Hg.
    - have Ht: P (jt_proj (JNode  (jt_rep (jt_proj xm)) (jt_rep (jt_proj xf)))).
      - exact: Hl (jt_proj xm) (jt_proj xf) hxm hxf.
      have Ht2: jt_proj (JNode  (jt_rep (jt_proj xm)) (jt_rep (jt_proj xf)))
          = jt_proj (JNode xm xf).
      - apply jt_proj_ker.
        simpl; unfold jt_equiv'.
        apply /jt_expression_beqP.
        rewrite (jt_rep_proj_cancel xm).
        rewrite (jt_rep_proj_cancel xf).
        simpl.
        rewrite (jt_reduction_is_idempotent xm).
        rewrite (jt_reduction_is_idempotent xf).
        by [].
      rewrite -Ht2.
      exact: Ht.
    - have Ht:  P (jt_proj (JLeft (jt_rep (jt_proj xl)))).
      - exact: Ha0 (jt_proj xl) hxl.
      have Ht2 : jt_proj (JLeft (jt_rep (jt_proj xl))) = jt_proj (JLeft xl).
      - apply jt_proj_ker.
        simpl; unfold jt_equiv'.
        apply /jt_expression_beqP.
        rewrite (jt_rep_proj_cancel xl); simpl.
        rewrite (jt_reduction_is_idempotent xl).
        by [].
      rewrite -Ht2.
      exact: Ht.
    - have Ht :
          P (jt_proj (JRight (jt_rep (jt_proj xr)))).
      - exact: Ha1 (jt_proj xr) hxr.
      have Ht2: jt_proj (JRight (jt_rep (jt_proj xr))) =  jt_proj (JRight xr).
      - apply jt_proj_ker.
        simpl; unfold jt_equiv'.
        apply /jt_expression_beqP.
        rewrite (jt_rep_proj_cancel xr); simpl; rewrite (jt_reduction_is_idempotent xr) //.
      rewrite -Ht2.
      exact: Ht.
  move => x.
  rewrite -(jt_proj_rep_cancel x); exact: goal (jt_rep x).
Qed.


Lemma jt_elt_ind : forall (P : jt_elt -> Prop),
  P jt_gen 
  -> (forall t', P t' -> P (jt_alpha_0 t'))
  -> (forall t', P t' -> P (jt_alpha_1 t'))
  -> (forall s' t', P s' -> P t' -> P (jt_lambda s' t')) 
  -> forall t, P t.
Proof.
  move => P Hg Ha0 Ha1 Hl.
  exact: jt_elt_rec P Hg Ha0 Ha1 Hl.
Qed.

Lemma jt_hom_determined_by_gen (f g: TV): 
TV_act f jt_gen = TV_act g jt_gen ->
 TV_eq f g.
Proof.
case: f => f Hf; case: g => g Hg.
unfold TV_eq; simpl.
intro gen_eq.
apply (@functional_extensionality_dep jt_elt (fun _ => jt_elt)).
set P :(jt_elt -> Prop):= fun x => (f x = g x).
apply (jt_elt_ind P).
exact: gen_eq.
move => t; unfold P.
rewrite ((Hf.1) t); rewrite ((Hg.1) t).
move => h; by rewrite h.
move => t; unfold P.
rewrite ((Hf.2.1) t); rewrite ((Hg.2.1) t).
move => h; by rewrite h.
move => s t; unfold P.
rewrite ((Hf.2.2) s t); rewrite ((Hg.2.2) s t).
move => hs ht.
rewrite hs; rewrite ht //.
Qed.

Lemma jt_equiv'_JLeft :
  forall x y,
    jt_equiv' x y ->
    jt_equiv' (JLeft x) (JLeft y).
Proof.
  move=> x y h.
  apply /jt_expression_beqP.
  have h' : jt_reduce_exp x = jt_reduce_exp y.
  - apply /jt_expression_beqP; exact h.
  simpl.
  rewrite h' //.
Qed.
Lemma jt_equiv'_JRight :
  forall x y,
    jt_equiv' x y ->
    jt_equiv' (JRight x) (JRight y).
Proof.
  move=> x y h.
  apply /jt_expression_beqP.
  have h' : jt_reduce_exp x = jt_reduce_exp y.
  - apply /jt_expression_beqP; exact h.
  simpl.
  rewrite h' //.
Qed.
Lemma jt_equiv'_JNode :
  forall x1 x2 y1 y2,
    jt_equiv' x1 y1 ->
    jt_equiv' x2 y2 ->
    jt_equiv' (JNode x1 x2) (JNode y1 y2).
Proof.
  move=> x1 x2 y1 y2 h1 h2.
  unfold jt_equiv' in *.
  apply /jt_expression_beqP.
  simpl.
  have h1' : jt_reduce_exp x1 = jt_reduce_exp y1.
  - apply /jt_expression_beqP; exact h1.
  have h2' : jt_reduce_exp x2 = jt_reduce_exp y2.
  - apply /jt_expression_beqP; exact h2.
  rewrite h1'; rewrite h2'.
  clear h1 h1'.
  elim: jt_reduce_exp y1 => [|jym jyf|jyl|jyr] //.
Qed.

Fixpoint is_uncancellable (x : jt_expression) : bool :=
  match x with
  | JEmpty => true
  | JLeft y =>
      match y with
      | JEmpty => true
      | JLeft z => is_uncancellable y
      | JRight z => is_uncancellable y
      | JNode z a => false
      end
  | JRight y =>
      match y with
      | JEmpty => true
      | JLeft z => is_uncancellable y
      | JRight z => is_uncancellable y
      | JNode z a => false
      end
  | JNode y z =>
      match y, z with
      | JLeft a, JRight b =>
          negb (jt_expression_beq a b) &&
          is_uncancellable y &&
          is_uncancellable z
      | _, _ => is_uncancellable y && is_uncancellable z
      end
  end.

Lemma dont_reduce_reduced (x : jt_expression): is_uncancellable x -> jt_reduce_exp x = x.
Proof.
have inductversion: forall (n:nat), forall (x : jt_expression), jt_depth x <= n -> is_uncancellable x -> jt_reduce_exp x = x.
- induction n. move => y hy.
  rewrite (depth_at_most_zero_is_empty y hy) //.
- move => y h1 h2.
  case yhype: y => [//|yl yr|yl|yr].
  - rewrite yhype in h1.
    simpl in h1.
    have hyl:jt_depth yl <= n. by lia. have hyr:jt_depth yr <= n. by lia.
    have hyl2: jt_reduce_exp yl = yl.
    - rewrite yhype in h2.
      have hyl3: is_uncancellable yl.
      - simpl in h2.
        case ylhype: yl => [//|yll ylr|yll|ylr].
        - rewrite ylhype in h2; rewrite -ylhype in h2; rewrite -ylhype; exact (andP h2).1.
        - rewrite ylhype in h2; rewrite -ylhype in h2; rewrite -ylhype.
          case yrhype: yr => [|yrl yrr|yrl|yrr].
          - all: try rewrite yrhype in h2; try rewrite -yrhype in h2; try exact (andP h2).1.
          exact: (andP ((andP h2).1)).2.
        - rewrite -ylhype; rewrite ylhype in h2; rewrite -ylhype in h2; exact (andP h2).1.
      exact: (IHn yl) hyl hyl3.
  - simpl; rewrite hyl2.
    have hyr2: jt_reduce_exp yr = yr.
    - rewrite yhype in h2.
      have hyr3: is_uncancellable yr.
      - simpl in h2.
        case ylhype: yl => [|yll ylr|yll|ylr].
        - all: try rewrite ylhype in h2; try rewrite -ylhype in h2.
        - exact (andP h2).2. exact (andP h2).2.
          case yrhype: yr => [//|yrl yrr|yrl|yrr].
          - rewrite yrhype in h2; rewrite -yrhype in h2; rewrite -yrhype; exact (andP h2).2.
          - rewrite yrhype in h2; rewrite -yrhype in h2; rewrite -yrhype; exact (andP h2).2.
          - rewrite yrhype in h2; rewrite -yrhype in h2; rewrite -yrhype; exact (andP h2).2.
          exact: (andP h2).2.
      exact: (IHn yr) hyr hyr3.
    rewrite hyr2.
    case ylhype: yl => [|yll ylr|yll|ylr] //. case yrhype: yr => [|yrl yrr|yrl|yrr] //.
    set casehype := jt_expression_beq yll yrr.
    case ch: casehype.
    rewrite yhype in h2; simpl in h2; rewrite ylhype in h2; rewrite yrhype in h2.
    have hbad: ~~ jt_expression_beq yll yrr. exact: (andP (andP h2).1).1.
    have hbad2: jt_expression_beq yll yrr. by [].
    move/negPf in hbad. move: hbad2. rewrite hbad.
    all: try by [].
    have hyl2: jt_reduce_exp yl = yl.
    - rewrite yhype in h2.
    - have hyl3: is_uncancellable yl.
      - simpl in h2.
        case ylhype: yl => [|yll ylr|yll|ylr] //.
        - all: try rewrite ylhype in h2; try by [].
      rewrite yhype in h1; simpl in h1; exact: (IHn yl) h1 hyl3.
    simpl; rewrite hyl2.
    case ylhype: yl => [|yll ylr|yll|ylr] //.
    rewrite yhype in h2; by rewrite ylhype in h2.

have hyr2: jt_reduce_exp yr = yr.
- rewrite yhype in h2.
  have hyr3: is_uncancellable yr.
  - simpl in h2.
    case yrhype: yr => [|yrl yrr|yrl|yrr] //.
    all: try rewrite yrhype in h2; try by [].
  rewrite yhype in h1; simpl in h1; exact: (IHn yr) h1 hyr3.
simpl; rewrite hyr2.
case yrhype: yr => [|yrl yrr|yrl|yrr] //.
rewrite yhype in h2; by rewrite yrhype in h2.

exact: inductversion (jt_depth x) x (leqnn (jt_depth x)).
Qed.


Lemma inductive_reduced (a : jt_expression): ((jt_reduce_exp a = JEmpty) \/
(exists (b : jt_expression), jt_reduce_exp a = JLeft (jt_reduce_exp b)) \/
(exists (b : jt_expression), jt_reduce_exp a = JRight (jt_reduce_exp b)) \/
(exists (b c : jt_expression), jt_reduce_exp a = JNode (jt_reduce_exp b) (jt_reduce_exp c)))
/\ is_uncancellable (jt_reduce_exp a). 
Proof.

Definition conclusion1 (x : jt_expression):= (jt_reduce_exp x = JEmpty) \/
(exists (y : jt_expression), jt_reduce_exp x = JLeft (jt_reduce_exp y)) \/
(exists (y : jt_expression), jt_reduce_exp x = JRight (jt_reduce_exp y)) \/
(exists (y z : jt_expression), jt_reduce_exp x = JNode (jt_reduce_exp y) (jt_reduce_exp z)).
Definition conclusion2 (x : jt_expression):= is_uncancellable (jt_reduce_exp x).
Definition induct_claim_n (n: nat) := forall (x: jt_expression), (jt_depth (x) <= n) -> conclusion1 x /\ conclusion2 x.

have base: induct_claim_n 0.
- unfold induct_claim_n.
- move => x h.
  split.
  - left. by rewrite (depth_at_most_zero_is_empty (x) h).
  by rewrite (depth_at_most_zero_is_empty (x) h).

have strong_induction_hype: forall (n: nat), induct_claim_n n -> induct_claim_n (S n).

2:
{
have all_claims: forall (n: nat), induct_claim_n n.
induction n.
exact: base.
exact: strong_induction_hype n IHn.
exact: all_claims (jt_depth ( a)) a (leqnn (jt_depth ( a))).
}

unfold induct_claim_n.
move => n induct_hype x.
case Hx: x => [|xm xf|xl|xr] .
  all: try split.
- by left.
- by [].

(* conclusion1 node *)
- unfold conclusion1.
  simpl.
  set xmj := jt_reduce_exp xm.
  case Hxmj: xmj => [|xmjm xmjf|xmjl|xmjr].
  - right. right. right.
    exists JEmpty. by exists xf.
  - rewrite -Hxmj.
    right. right. right.
    exists xm. by exists xf.
set xfj := jt_reduce_exp xf.
case Hxfj: xfj => [|xfjm xfjf|xfjl|xfjr].
right. right. right.
exists xm.
exists JEmpty.
by rewrite -Hxmj.
rewrite -Hxfj.
rewrite -Hxmj.
right. right. right.
exists xm. by exists xf.
rewrite -Hxfj.
rewrite -Hxmj.
right. right. right.
exists xm.
exists xf.
by [].
set casebool := jt_expression_beq xmjl xfjr.
case cbH: casebool.
have shallowxm: jt_depth xm <= n.
simpl in H.
by lia.
have conc2xm: conclusion2 xm.
exact (induct_hype xm shallowxm).2.
unfold conclusion2 in conc2xm.
rewrite -/xmj in conc2xm.
have redtarg: is_uncancellable xmjl.
rewrite Hxmj in conc2xm.
simpl in conc2xm.
case Hxmjl: xmjl => [|xmjlm xmjlf|xmjll|xmjlr] //.
rewrite Hxmjl in conc2xm.
by [].
rewrite Hxmjl in conc2xm.
by [].
rewrite Hxmjl in conc2xm.
by [].
have shallowxmjl: jt_depth xmjl <= n.
have temp1: jt_depth xmjl <= jt_depth xmj.
rewrite Hxmj.
simpl.
by lia.
have temp2: jt_depth xmj <= jt_depth xm.
exact: reducing_reduces_depth xm.
by lia.
have conc1xmjl: conclusion1 xmjl.
exact: (induct_hype xmjl shallowxmjl).1.
unfold conclusion1 in conc1xmjl.
have alred: jt_reduce_exp xmjl = xmjl.
exact: dont_reduce_reduced redtarg.
rewrite alred in conc1xmjl. 
by [].
right.
right.
right.
exists xm.
exists xf.
rewrite -Hxmj.
rewrite -Hxfj.
by [].
right.
right.
right.
rewrite -Hxmj.
exists xm.
exists xf.
by [].
(* conclusion2 node *)
unfold conclusion2.
simpl.
set xmj := jt_reduce_exp xm.
set xfj := jt_reduce_exp xf.
simpl in H.
have shallow_xm: jt_depth xm <=n.
by lia.
have shallow_xf: jt_depth xf <=n.
by lia.
have shallow_xmj: jt_depth xmj <=n.
have Ht: jt_depth (jt_reduce_exp xm) <= jt_depth xm.
exact: reducing_reduces_depth xm.
rewrite -/xmj in Ht.
by lia.
have shallow_xfj: jt_depth xfj <=n.
have Ht: jt_depth (jt_reduce_exp xf) <= jt_depth xf.
exact: reducing_reduces_depth xf.
rewrite -/xfj in Ht.
by lia.
have HRxmj: is_uncancellable xmj.
exact: (induct_hype xm shallow_xm).2.
have HRxfj: is_uncancellable xfj.
exact: (induct_hype xf shallow_xf).2.
case Hxmj: xmj => [|xmjm xmjf|xmjl|xmjr].
simpl.
exact: HRxfj.
simpl.
case Hxmjm: xmjm => [|xmjmm xmjmf|xmjml|xmjmr].
have goal1: is_reduced JEmpty.
by [].
have goal2: is_uncancellable xmjf.
rewrite Hxmj in HRxmj.
simpl in HRxmj.
rewrite Hxmjm in HRxmj.
exact (andP HRxmj).2.
have goal3: is_uncancellable xfj.
exact: HRxfj.
apply/andP.
by [].
apply/andP.
split.
rewrite Hxmj in HRxmj.
simpl in HRxmj.
rewrite Hxmjm in HRxmj.
by [].
by [].
rewrite Hxmj in HRxmj.
simpl in HRxmj.
rewrite Hxmjm in HRxmj.
case Hxmjf: xmjf => [|xmjfm xmjff|xmjfl|xmjfr].
all: try rewrite Hxmjf in HRxmj.
all: try rewrite -Hxmjm in HRxmj.
all: try rewrite -Hxmjm.
all: try apply/andP.
all: try split.
all: try apply/andP.
all: try split.
all: try exact: (andP HRxmj).1.
all: try by [].
all: try rewrite -Hxmjf in HRxmj.
all: try rewrite -Hxmjf.
all: try exact: (andP HRxmj).2.
all: try rewrite Hxmj in HRxmj.
all: try simpl in HRxmj.
all: try rewrite Hxmjm in HRxmj.
all: try rewrite -Hxmjm in HRxmj.
exact: (andP HRxmj).1.
exact: (andP HRxmj).2.
case Hxfj: xfj => [|xfjm xfjf|xfjl|xfjr].
all: try by [].
case Hxmjl: xmjl => [|xmjlm xmjlf|xmjll|xmjlr].
all: try rewrite Hxmjl in HRxmj.
by [].
all: try rewrite -Hxmjl.
all: try rewrite -Hxmj.
by simpl.
simpl.
rewrite Hxmj.
apply/andP.
split.
rewrite -Hxmjl in HRxmj.
simpl.
rewrite Hxmjl.
rewrite -Hxmjl.
by [].
by [].
simpl.
rewrite Hxmj.
apply/andP.
split.
rewrite -Hxmjl in  HRxmj.
simpl.
rewrite Hxmjl.
rewrite -Hxmjl.
by [].
by [].
rewrite -Hxfj.
simpl.
rewrite Hxmj.
rewrite Hxfj.
apply/andP.
split.
simpl.
exact: HRxmj.
rewrite -Hxfj.
by [].
simpl.
rewrite Hxmj.
apply/andP.
split.
simpl.
exact: HRxmj.
simpl in HRxfj.
rewrite Hxfj in HRxfj.
by [].
set casesplit := jt_expression_beq xmjl xfjr.
case ch: casesplit.
simpl.
case Hxmjl: xmjl => [|xmjlm xmjlf|xmjll|xmjlr].
by [].
all: try rewrite -Hxmjl.
all: try rewrite Hxmjl in HRxmj.
all: try rewrite -Hxmjl in HRxmj.
all: try by [].
rewrite -Hxfj.
simpl.
rewrite Hxmj.
rewrite Hxfj.
rewrite -Hxmj.
rewrite -Hxfj.
apply/andP.
split.
apply/andP.
split.
rewrite -/casesplit.
rewrite ch.
by [].
rewrite  Hxmj.
simpl.
by [].
by [].
(* conclusion1 left *)
unfold conclusion1.
simpl.
set xlj := jt_reduce_exp xl.
have shallowxl : jt_depth xl <= n.
simpl in H.
by lia.
have conc1xl: conclusion1 xl.
exact: (induct_hype xl shallowxl).1.
have conc2cl: conclusion2 xl.
exact: (induct_hype xl shallowxl).2.
case: conc1xl.
intro h1.
rewrite -/xlj in h1.
rewrite h1.
right.
left.
exists JEmpty.
by [].
intro h2.
case h2.
intro h3.
rewrite -/xlj in h3.
unfold conclusion2 in conc2cl.
rewrite -/xlj in conc2cl.
case: h3 => [y hy].
rewrite hy.
set yj := jt_reduce_exp y.
rewrite -hy.
right.
left.
exists xlj.
have Heq:  (jt_reduce_exp xlj) = xlj.
exact: dont_reduce_reduced xlj conc2cl.
rewrite Heq.
by [].
rewrite -/xlj.
intro h3.
case Hxlj: xlj => [|xljm xljf|xljl|xljr].
right.
left.
exists JEmpty.
by [].
case h3.
intro h4.
case: h4 => [y hy].
rewrite hy in Hxlj.
by [].
intro h4.
case: h4 => [y h4].
case: h4 => [z h4].
rewrite Hxlj in h4.
case h2.
intro h5.
case h5 => [d hd].
rewrite -/xlj in hd.
rewrite Hxlj in hd.
by [].
rewrite -/xlj.
intro h6.
have red_xljm: is_uncancellable xljm.
unfold conclusion2 in conc2cl.
rewrite -/xlj in conc2cl.
rewrite Hxlj in conc2cl.
simpl in conc2cl.
case Hxljm: xljm => [|xljmm xljmf|xljml|xljmr].
all: try rewrite Hxljm in conc2cl.
by [].
exact: (andP conc2cl).1.
case Hxljf: xljf => [|xljfm xljff|xljfl|xljfr].
all: try rewrite Hxljf in conc2cl.
exact: (andP conc2cl).1.
exact: (andP conc2cl).1.
exact: (andP conc2cl).1.
exact: (andP (andP conc2cl).1).2.
exact: (andP conc2cl).1.
have Heq:  (jt_reduce_exp xljm) = xljm.
exact: dont_reduce_reduced xljm red_xljm.
case Hxljm: xljm => [|xljmm xljmf|xljml|xljmr].
by left.
right.
right.
right.
exists xljmm.
exists xljmf.
have red_xljmm: (is_uncancellable xljmm) /\ (is_uncancellable xljmf).
rewrite Hxljm in red_xljm.
simpl in red_xljm.
case Hxljmm: xljmm => [|xljmmm xljmmf|xljmml|xljmmr].
split.
by [].
all: try rewrite Hxljmm in red_xljm.
exact: (andP red_xljm).2.
exact: (andP red_xljm).
case Hxljmf: xljmf => [|xljmfm xljmff|xljmfl|xljmfr].
all: try  rewrite Hxljmf in red_xljm.
exact: (andP red_xljm).
exact: (andP red_xljm).
exact: (andP red_xljm).
split.
3: split.
exact: (andP (andP red_xljm).1).2.
exact: (andP red_xljm).2.
exact: (andP red_xljm).1.
exact: (andP red_xljm).2.
rewrite (dont_reduce_reduced xljmm red_xljmm.1).
rewrite (dont_reduce_reduced xljmf red_xljmm.2).
by [].
right.
left.
exists xljml.
have red_xljml: is_uncancellable xljml.
rewrite Hxljm in red_xljm.
simpl in red_xljm.
case Hxljml: xljml => [|xljmlm xljmlf|xljmll|xljmlr] //.
all: try rewrite Hxljml in red_xljm.
all: try by [].
have Heql:  (jt_reduce_exp xljml) = xljml.
exact: dont_reduce_reduced xljml red_xljml.
rewrite Heql.
by [].
right. right. left.
have red_xljmr: is_uncancellable xljmr.
rewrite Hxljm in red_xljm.
simpl in red_xljm.
case Hxljmr: xljmr => [|xljmrm xljmrf|xljmrl|xljmrr] //.
all: try rewrite Hxljmr in red_xljm.
all: try by [].
have Heqr : (jt_reduce_exp xljmr) = xljmr.
exact: dont_reduce_reduced xljmr red_xljmr.
exists xljmr.
by rewrite Heqr.
rewrite -Hxlj.
right. left.
by exists xl.
right. left.
rewrite -Hxlj.
by exists xl.
(* conclusion2 left *)
unfold conclusion2.
simpl.
set xlj:= jt_reduce_exp xl.
case Hxlj: xlj => [|xljm xljf|xljl|xljr].
by [].
have shallowxl : jt_depth xl <= n.
simpl in H.
by lia.
have conc1xl: conclusion1 xl.
exact: (induct_hype xl shallowxl).1.
have conc2cl: conclusion2 xl.
exact: (induct_hype xl shallowxl).2.
unfold conclusion2 in conc2cl.
rewrite -/xlj in conc2cl.
rewrite Hxlj in conc2cl.
simpl in conc2cl.
case Hxljm: xljm => [|xljmm xljmf|xljml|xljmr] //.
all: try rewrite Hxljm in conc2cl.
all: try exact: (andP conc2cl).1.
case Hxljf: xljf => [|xljfm xljff|xljfl|xljfr].
all: try rewrite Hxljf in conc2cl.
all: try exact: (andP conc2cl).1.
exact: (andP (andP conc2cl).1).2.
all: try rewrite -Hxlj.
all: try simpl.
all: try rewrite Hxlj.
all: try rewrite -Hxlj.
all: try have shallowxl : jt_depth xl <= n.
all: try simpl in H.
all: try by lia.
all: try have conc1xl: conclusion1 xl.
all: try exact: (induct_hype xl shallowxl).1.
all: try have conc2cl: conclusion2 xl.
all: try exact: (induct_hype xl shallowxl).2.
(* conclusion1 right *)
unfold conclusion1.
simpl.
set xrj := jt_reduce_exp xr.
have shallowxr : jt_depth xr <= n.
simpl in H.
by lia.
have conc1xr: conclusion1 xr.
exact: (induct_hype xr shallowxr).1.
have conc2cl: conclusion2 xr.
exact: (induct_hype xr shallowxr).2.
case: conc1xr.
intro h1.
rewrite -/xrj in h1.
rewrite h1.
right. right. left. by exists JEmpty.
intro h2.
case h2.
intro h3.
rewrite -/xrj in h3.
unfold conclusion2 in conc2cl.
rewrite -/xrj in conc2cl.
case: h3 => [y hy].
rewrite hy.
set yj := jt_reduce_exp y.
rewrite -hy.
right. right. left.
exists xrj.
have Heq:  (jt_reduce_exp xrj) = xrj.
exact: dont_reduce_reduced xrj conc2cl.
rewrite Heq.
by [].
rewrite -/xrj.
intro h3.
case Hxrj: xrj => [|xrjm xrjf|xrjl|xrjr].
right. right. left.
by exists JEmpty.
case h3.
intro h4.
case: h4 => [y hy].
by rewrite hy in Hxrj.
intro h4.
case: h4 => [y h4].
case: h4 => [z h4].
rewrite Hxrj in h4.
case h2.
intro h5.
case h5 => [d hd].
rewrite -/xrj in hd.
by rewrite Hxrj in hd.
rewrite -/xrj.
intro h6.
have red_xrjf: is_uncancellable xrjf.
unfold conclusion2 in conc2cl.
rewrite -/xrj in conc2cl.
rewrite Hxrj in conc2cl.
simpl in conc2cl.
case Hxrjm: xrjm => [|xrjmm xrjmf|xrjml|xrjmr].
all: try rewrite Hxrjm in conc2cl.
by [].
exact: (andP conc2cl).2.
case Hxrjf: xrjf => [|xrjfm xrjff|xrjfl|xrjfr].
all: try rewrite Hxrjf in conc2cl.
all: try exact: (andP conc2cl).2.
have Heq:  (jt_reduce_exp xrjf) = xrjf.
exact: dont_reduce_reduced xrjf red_xrjf.
case Hxrjf: xrjf => [|xrjfm xrjff|xrjfl|xrjfr].
by left.
right. right. right.
exists xrjfm. exists xrjff.
have red_xrjfm: (is_uncancellable xrjfm) /\ (is_uncancellable xrjff).
rewrite Hxrjf in red_xrjf.
simpl in red_xrjf.
case Hxrjfm: xrjfm => [|xrjfmm xrjfmf|xrjfml|xrjfmr] //.
split.
by [].
all: try rewrite Hxrjfm in red_xrjf.
exact: (andP red_xrjf).2.
exact: (andP red_xrjf).
case Hxrjff: xrjff => [|xrjffm xrjfff|xrjffl|xrjffr].
all: try rewrite Hxrjff in red_xrjf.
all: try exact: (andP red_xrjf).
split.
exact: (andP (andP red_xrjf).1).2.
exact: (andP red_xrjf).2.
rewrite (dont_reduce_reduced xrjfm red_xrjfm.1).
by rewrite (dont_reduce_reduced xrjff red_xrjfm.2).
right. left.
exists xrjfl.
have red_xrjfl: is_uncancellable xrjfl.
rewrite Hxrjf in red_xrjf.
simpl in red_xrjf.
case Hxrjfl: xrjfl => [|xrjflm xrjflf|xrjfll|xrjflr] //.
all: try rewrite Hxrjfl in red_xrjf.
all: try by [].
have Heqr:  (jt_reduce_exp xrjfl) = xrjfl.
exact: dont_reduce_reduced xrjfl red_xrjfl.
by rewrite Heqr.
right. right. left.
have red_xrjfr: is_uncancellable xrjfr.
rewrite Hxrjf in red_xrjf.
simpl in red_xrjf.
case Hxrjfr: xrjfr => [|xrjfrm xrjfrf|xrjfrl|xrjfrr].
all: try rewrite Hxrjfr in red_xrjf.
all: try by [].
have Heqr : (jt_reduce_exp xrjfr) = xrjfr.
exact: dont_reduce_reduced xrjfr red_xrjfr.
exists xrjfr.
by rewrite Heqr.
rewrite -Hxrj.
right; right; left; by exists xr.
right; right; left; rewrite -Hxrj; by exists xr.
(* conclusion2 right *)
unfold conclusion2.
simpl.
set xrj:= jt_reduce_exp xr.
case Hxrj: xrj => [|xrjm xrjf|xrjl|xrjr] //.
have shallowxr : jt_depth xr <= n. simpl in H. by lia.
have conc1xr: conclusion1 xr. exact: (induct_hype xr shallowxr).1.
have conc2cl: conclusion2 xr. exact: (induct_hype xr shallowxr).2.
unfold conclusion2 in conc2cl.
rewrite -/xrj in conc2cl; rewrite Hxrj in conc2cl; simpl in conc2cl.
case Hxrjm: xrjm => [|xrjmm xrjmf|xrjml|xrjmr].
all: try rewrite Hxrjm in conc2cl.
all: try exact: (andP conc2cl).2.
case Hxrjf: xrjf => [|xrjfm xrjff|xrjfl|xrjfr].
all: try rewrite Hxrjf in conc2cl.
all: try by [].
all: try exact: (andP conc2cl).2.
all: try rewrite -Hxrj.
all: try simpl.
all: try rewrite Hxrj.
all: try rewrite -Hxrj.
all: try have shallowxr : jt_depth xr <= n.
all: try simpl in H.
all: try by lia.
all: try have conc1xr: conclusion1 xr.
all: try exact: (induct_hype xr shallowxr).1.
all: try have conc2cl: conclusion2 xr.
all: try exact: (induct_hype xr shallowxr).2.
Qed.

Lemma is_reduced_reduced_iff_is_uncancellable (x : jt_expression): 
(is_uncancellable x <-> 
is_reduced x)  /\ 
(is_uncancellable x <-> exists (y : jt_expression), jt_reduce_exp y = x).
Proof.
split. split. 3: split.
move => h; apply /jt_expression_beqP.
by rewrite (dont_reduce_reduced x h).
intro h.
have h': x = (jt_reduce_exp x).
- apply /jt_expression_beqP.
  exact: h.
rewrite h'; exact: (inductive_reduced x).2.
intro h; exists x; exact: dont_reduce_reduced x h.
intro h; case h=> [y hy].
rewrite -hy; exact: (inductive_reduced y).2.
Qed.

Lemma jt_pass_down_reduction : 
(forall (x y: jt_expression),  jt_reduce_exp (JNode x y) = (JNode x y) -> (jt_reduce_exp x = x /\ jt_reduce_exp y = y))
/\ (forall (x: jt_expression),  jt_reduce_exp (JLeft x) = (JLeft x) -> (jt_reduce_exp x = x))
/\ (forall (x: jt_expression),  jt_reduce_exp (JRight x) = (JRight x) -> (jt_reduce_exp x = x)).
Proof.
split. 2: split.
move => x y H.
have h1: is_uncancellable (JNode x y).
- apply (is_reduced_reduced_iff_is_uncancellable (JNode x y)).2.2.
  exists (JNode x y).
  exact H.
have h2: is_uncancellable x /\ is_uncancellable y.
- simpl in h1.
  case Hx:x => [|xm xf|xl|xr]//.
  - all: try rewrite Hx in h1.
    all: try apply/andP.
    all: try by [].
    case Hy:y => [|ym yf|yl|yr]//.
    - all: try rewrite Hy in h1.
      all: try by [].
      apply/ andP.
      split.
      exact (andP (andP h1).1).2 .
      exact (andP h1).2.
    split.
    apply /jt_expression_beqP.
    2: apply /jt_expression_beqP.
    have red_x: is_reduced x.
    - exact: (is_reduced_reduced_iff_is_uncancellable x).1.1 h2.1.
    unfold is_reduced in red_x.
    rewrite (jt_expression_beq_sym (jt_reduce_exp x) x).
    exact: red_x.
    have red_y: is_reduced y.
    - exact: (is_reduced_reduced_iff_is_uncancellable y).1.1 h2.2.
    unfold is_reduced in red_y.
    rewrite (jt_expression_beq_sym (jt_reduce_exp y) y).
    exact: red_y.
move => x H.
have h1: is_uncancellable (JLeft x).
- apply (is_reduced_reduced_iff_is_uncancellable (JLeft x)).2.2.
  exists (JLeft x).
  exact H.
have h2: is_uncancellable x.
- simpl in h1.
  case Hx:x => [|xm xf|xl|xr]//.
  - all: try by rewrite Hx in h1.
  apply /jt_expression_beqP.
  rewrite (jt_expression_beq_sym (jt_reduce_exp x) x).
  exact: (is_reduced_reduced_iff_is_uncancellable x).1.1 h2.
move => x H.
have h1: is_uncancellable (JRight x).
- apply (is_reduced_reduced_iff_is_uncancellable (JRight x)).2.2.
  exists (JRight x).
  exact H.
have h2: is_uncancellable x.
- simpl in h1.
  case Hx:x => [|xm xf|xl|xr]//.
  - all: try by rewrite Hx in h1.
  apply /jt_expression_beqP.
  rewrite (jt_expression_beq_sym (jt_reduce_exp x) x).
  exact: (is_reduced_reduced_iff_is_uncancellable x).1.1 h2.
Qed.

Lemma jt_equiv'_left_node :
  forall a b,
    jt_equiv' (JLeft (JNode a b)) a.
Proof.
  move=> a b.
  unfold jt_equiv'.
  apply /jt_expression_beqP.
  case E1: (jt_reduce_exp a) =>
    [|a1 a2|a1|a1];
  case E2: (jt_reduce_exp b) =>
    [|b1 b2|b1|b1].
  all: simpl.
  all: try rewrite E1.
  all: try rewrite E2.
  all: try reflexivity.
  case H : (jt_expression_beq a1 b1).
  - set a1' := a1.
    case Ha1: a1' => [|a11 a12|a11|a11] //.
    rewrite -/a1' in E1; rewrite Ha1 in E1.
    have Ht: is_uncancellable (JLeft (JNode a11 a12)).
    - apply (is_reduced_reduced_iff_is_uncancellable (JLeft (JNode a11 a12))).2.2.
      exists a; exact: E1.
    by [].
  - reflexivity.
Qed.

Lemma jt_equiv'_right_node :
  forall a b,
    jt_equiv' (JRight (JNode a b)) b.
Proof.
  move=> a b.
  unfold jt_equiv'.
  apply /jt_expression_beqP.
  case E1: (jt_reduce_exp a) =>
    [|a1 a2|a1|a1];
  case E2: (jt_reduce_exp b) =>
    [|b1 b2|b1|b1] //.
  all: simpl.
  all: try rewrite E1.
  all: try rewrite E2.
  all: try reflexivity.
  case H : (jt_expression_beq a1 b1).
  - set a1' := a1.
    have bea: a1 = b1.
      by apply /jt_expression_beqP.
    rewrite -bea; rewrite -/a1'.
    case Ha1: a1' => [|a11 a12|a11|a11] //.
    rewrite -/a1' in E1; rewrite Ha1 in E1.
    have Ht: is_uncancellable (JLeft (JNode a11 a12)).
    - apply (is_reduced_reduced_iff_is_uncancellable (JLeft (JNode a11 a12))).2.2.
      exists a; exact: E1.
    by [].
  - reflexivity.
Qed.

Lemma jt_equiv'_cancel :
  forall a b,
    jt_equiv' a b ->
    jt_equiv' (JNode (JLeft a) (JRight b)) a.
Proof.
  move=> a b.
  unfold jt_equiv'.
  move => h.
  have conv (x y:jt_expression): jt_expression_beq x y -> x = y.
  -  move => h1.
     by apply /jt_expression_beqP.
  have aeb: (jt_reduce_exp a) = (jt_reduce_exp b).
    exact: (conv (jt_reduce_exp a) (jt_reduce_exp b)) h.
  apply /jt_expression_beqP.
  simpl.
  all: try rewrite -aeb.
  case E1: (jt_reduce_exp a) =>
    [|a1 a2|al|ar] //.
  all: try case E2: a1 =>
    [|a11 a12|a11|a11] //.
  all: try case E3: a2 =>
    [|a21 a22|a21|a21] //.
  all: try case h2:(jt_expression_beq a11 a21); try apply conv in h2; try rewrite h2.
  all: try case h3:(jt_expression_beq (JLeft (JNode a11 a12)) (JLeft (JNode a11 a12))); try apply conv in h3; try rewrite h3.
  all: try case h4:(jt_expression_beq (JLeft (JLeft a11)) (JLeft (JLeft a11))); try apply conv in h4; try rewrite h4.
  all: try case h5:(jt_expression_beq (JRight (JNode a11 a12)) (JRight (JNode a11 a12))); try apply conv in h5; try rewrite h5.
  all: try case h6:(jt_expression_beq (JRight (JLeft a11)) (JRight (JLeft a11))); try apply conv in h6; try rewrite h6.
  all: try case h7:(jt_expression_beq (JRight (JRight a11)) (JRight (JRight a11))); try apply conv in h7; try rewrite h6.
  all: try case h8:(jt_expression_beq (JLeft (JRight a11)) (JLeft (JRight a11))); try apply conv in h8; try rewrite h8.
  all: try by [].
  all: try have Ht: is_uncancellable (JNode a1 a2).
  all: try apply (is_reduced_reduced_iff_is_uncancellable (JNode a1 a2)).2.2.
  all: try exists a; try by [].
  all: try have Ht: is_uncancellable (JLeft al).
  all: try apply (is_reduced_reduced_iff_is_uncancellable (JLeft al)).2.2.
  all: try exists a; try by [].
  all: try have Ht: is_uncancellable (JRight ar).
  all: try apply (is_reduced_reduced_iff_is_uncancellable (JRight ar)).2.2.
  all: try exists a; try by [].
  all: try rewrite E2 in Ht.
  all: try rewrite E3 in Ht.
  all: try rewrite h2 in Ht.
  all: try simpl in Ht.
  all: try rewrite (jt_expression_beq_refl a21) in Ht.
  all: try by simpl in Ht.
  by rewrite (jt_expression_beq_refl (JLeft al)).
  by rewrite (jt_expression_beq_refl (JRight ar)).
Qed.

(*
Fixpoint jt_rec_exp (x : jt_elt) (e : jt_expression) : jt_expression :=
  match e with
  | JEmpty => jt_rep x
  | JNode a b => JNode (jt_rec_exp x a) (jt_rec_exp x b)
  | JLeft a => JLeft (jt_rec_exp x a)
  | JRight a => JRight (jt_rec_exp x a)
  end.
 *)


Definition is_jt_algebra (T: Type) (lambda : T -> T -> T) (alpha_0 : T -> T) (alpha_1 : T -> T): 
Prop :=
(forall (x: T), lambda (alpha_0 x) (alpha_1 x) = x) /\
(forall (x y: T), alpha_0 (lambda x y) = x) /\
(forall (x y: T), alpha_1 (lambda x y) = y).


Lemma free_jt_is_jt_algebra: is_jt_algebra jt_elt jt_lambda jt_alpha_0 jt_alpha_1.
Proof.
split. 
unfold jt_lambda; unfold quotient_pass_2func; unfold jt_alpha_0; unfold jt_alpha_1; unfold quotient_pass_func.
move => x; try move => y.
rewrite (jt_rep_proj_cancel (JLeft (jt_rep x))); rewrite -(jt_proj_rep_cancel x).
apply jt_proj_ker.
rewrite (jt_proj_rep_cancel x).
rewrite jt_rep_proj_cancel.
set rx := (jt_rep x).
unfold jt_equiv; simpl.
unfold jt_equiv'.
apply /jt_expression_beqP.
have red_rx: rx = jt_reduce_exp rx. - rewrite /rx.
    unfold jt_rep.
    apply /jt_expression_beqP. 
    exact: jt_reduction_is_reduced (jt_rep_temp x).
  rewrite -red_rx.
  case Hrx: rx => [|rxm rxf|rxl|rxr] //.
  all: try rewrite -Hrx.
  by rewrite -red_rx.
  apply /jt_expression_beqP.
  rewrite red_rx.
  have Ht: jt_equiv' (JNode (JLeft rx) (JRight rx)) rx.
  - exact: (jt_equiv'_cancel rx rx) (jt_equiv'_refl rx).
  unfold jt_equiv' in Ht.
  rewrite -red_rx in Ht; rewrite -red_rx; exact: Ht.
simpl; rewrite -red_rx; rewrite Hrx.
by rewrite (jt_expression_beq_refl (JRight rxr)).

split.
move => x y.
set LHS := jt_alpha_0 (jt_lambda x y).
rewrite -(jt_proj_rep_cancel x); rewrite -(jt_proj_rep_cancel LHS);rewrite /LHS.
apply/ jt_proj_ker.
unfold jt_equiv; simpl.
have h1: jt_equiv' (JLeft (JNode (jt_rep x) (jt_rep y))) (jt_rep x).
- exact: jt_equiv'_left_node (jt_rep x) (jt_rep y).
have h2: jt_equiv' (jt_rep (jt_alpha_0 (jt_lambda x y))) (JLeft (JNode (jt_rep x) (jt_rep y))).
- set In := (JNode (jt_rep x) (jt_rep y)).
- have h3: jt_equiv' (jt_rep (jt_proj In)) In.
  - rewrite (jt_rep_proj_cancel In).
    unfold  jt_equiv'.
    apply/ jt_expression_beqP.
    exact: jt_reduction_is_idempotent In.
  have h4: jt_equiv' (JLeft (jt_rep (jt_proj In))) (JLeft In).
  - exact: jt_equiv'_JLeft (jt_rep (jt_proj In)) In h3.
  have h5: jt_equiv' (jt_rep (jt_proj (JLeft (jt_rep (jt_proj In))))) (JLeft (jt_rep (jt_proj In))).
  - apply/ jt_proj_ker.
    by rewrite (jt_proj_rep_cancel (jt_proj (JLeft (jt_rep (jt_proj In))))).
  exact: jt_equiv'_trans (JLeft (jt_rep (jt_proj In))) (jt_rep (jt_proj (JLeft (jt_rep (jt_proj In))))) (JLeft In) h5 h4.
exact: jt_equiv'_trans (JLeft (JNode (jt_rep x) (jt_rep y))) (jt_rep (jt_alpha_0 (jt_lambda x y))) (jt_rep x) h2 h1.

move => x y.
set LHS := jt_alpha_1 (jt_lambda x y).
rewrite -(jt_proj_rep_cancel y); rewrite -(jt_proj_rep_cancel LHS); rewrite /LHS.
apply/ jt_proj_ker.
unfold jt_equiv; simpl.
have h1: jt_equiv' (JRight (JNode (jt_rep x) (jt_rep y))) (jt_rep y).
- exact: jt_equiv'_right_node (jt_rep x) (jt_rep y).
have h2: jt_equiv' (jt_rep (jt_alpha_1 (jt_lambda x y))) (JRight (JNode (jt_rep x) (jt_rep y))).
- set In := (JNode (jt_rep x) (jt_rep y)).
- have h3: jt_equiv' (jt_rep (jt_proj In)) In.
  - rewrite (jt_rep_proj_cancel In).
    unfold  jt_equiv'.
    apply/ jt_expression_beqP.
    exact: jt_reduction_is_idempotent In.
  have h4: jt_equiv' (JRight (jt_rep (jt_proj In))) (JRight In).
  - exact: jt_equiv'_JRight (jt_rep (jt_proj In)) In h3.
  have h5: jt_equiv' (jt_rep (jt_proj (JRight (jt_rep (jt_proj In))))) (JRight (jt_rep (jt_proj In))).
  - apply/ jt_proj_ker.
    by rewrite (jt_proj_rep_cancel (jt_proj (JRight (jt_rep (jt_proj In))))).
  exact: jt_equiv'_trans (JRight (jt_rep (jt_proj In))) (jt_rep (jt_proj (JRight (jt_rep (jt_proj In))))) (JRight In) h5 h4.
exact: jt_equiv'_trans (JRight (JNode (jt_rep x) (jt_rep y))) (jt_rep (jt_alpha_1 (jt_lambda x y))) (jt_rep y) h2 h1.
Qed.

Theorem jt_equiv_minimal :
  forall (R : jt_expression -> jt_expression -> Prop),
    (forall x, R x x) ->
    (forall x y, R x y -> R y x) ->
    (forall x y z, R x y -> R y z -> R x z)  ->
    (forall x y z a, R x y -> R z a -> R (JNode x z) (JNode y a) ) ->
    (forall x y, R x y -> R (JLeft x) (JLeft y)) ->
    (forall x y, R x y -> R (JRight x) (JRight y)) ->
    (forall x, R (JNode (JLeft x) (JRight x)) x) ->
    (forall x y, R (JLeft (JNode x y)) x) ->
    (forall x y, R (JRight (JNode x y)) y) ->
    (forall x y, (jt_equiv x y) -> (R x y)).
Proof.
Definition R_hype (R : jt_expression -> jt_expression -> Prop) (a:jt_expression): Prop :=  (R a (jt_reduce_exp a)).
move => R R_refl R_sym R_trans R_lambda_hom R_alpha_0_hom R_alpha_1_hom R_lambda_rel R_alpha_0_rel R_alpha_1_rel.
move => x y.
have R_red : forall (x:jt_expression), R x (jt_reduce_exp x).
  - have base_hype: forall (a:jt_expression), (jt_depth a <= 0) -> (R_hype R a).
    - move => a ha.
      rewrite (depth_at_most_zero_is_empty a ha). simpl. exact: R_refl.
  - have strong_induct: forall (n:nat), (forall (a:jt_expression), ((jt_depth a <= n) -> (R_hype R a))) -> (forall (a:jt_expression), ((jt_depth a <= (S n)) -> (R_hype R a))).
    - move => n Ih a.
      case Ha: a => [|am af|al|ar] //.
      - move => h.
        unfold R_hype.
        by simpl.
        move => h.
        unfold R_hype.
        have hm_shallow: jt_depth am <= n. simpl in h. by lia.
        have hf_shallow: jt_depth af <= n. simpl in h. by lia.
        set jam := (jt_reduce_exp am).
        case Hjam: jam => [|jamm jamf|jaml|jamr] //.
        - simpl.
          rewrite-/ jam. rewrite Hjam. rewrite- Hjam.
          exact: R_lambda_hom am jam af (jt_reduce_exp af) (Ih am hm_shallow) (Ih af hf_shallow).
        - simpl.
          rewrite-/ jam. rewrite Hjam. rewrite- Hjam.
          exact: R_lambda_hom am jam af (jt_reduce_exp af) (Ih am hm_shallow) (Ih af hf_shallow).
        - simpl.
          rewrite-/ jam. rewrite Hjam. rewrite- Hjam.
          set jaf := (jt_reduce_exp af).
          case Hjaf: jaf => [|jafm jaff|jafl|jafr] //.
          - unfold R_hype. rewrite -Hjaf.
            exact: R_lambda_hom am jam af jaf (Ih am hm_shallow) (Ih af hf_shallow).
          - unfold R_hype. rewrite -Hjaf.
            exact: R_lambda_hom am jam af jaf (Ih am hm_shallow) (Ih af hf_shallow).
          - unfold R_hype. rewrite -Hjaf.
            exact: R_lambda_hom am jam af jaf (Ih am hm_shallow) (Ih af hf_shallow).
          - case hc: (jt_expression_beq jaml jafr).
            - have ht: R (JNode am af) (JNode jam jaf). exact: R_lambda_hom am jam af jaf (Ih am hm_shallow) (Ih af hf_shallow).
              rewrite Hjam in ht; rewrite Hjaf in ht.
              have ht2 : R (JNode (JLeft jaml) (JRight jafr)) jaml.
              - have Heq: jaml = jafr. by apply / jt_expression_beqP.
                rewrite- Heq.
                exact: R_lambda_rel jaml.
              exact: R_trans (JNode am af) (JNode (JLeft jaml) (JRight jafr)) jaml ht ht2.
            - unfold R_hype. rewrite -Hjaf.
              exact: R_lambda_hom am jam af jaf (Ih am hm_shallow) (Ih af hf_shallow).
        - simpl.
          rewrite-/ jam. rewrite Hjam. rewrite- Hjam.
          exact: R_lambda_hom am jam af (jt_reduce_exp af) (Ih am hm_shallow) (Ih af hf_shallow).
      - move => h.
        unfold R_hype.
        have hl: jt_reduce_exp (JLeft al) = jt_reduce_exp (JLeft (jt_reduce_exp al)).
        - simpl. by rewrite (jt_reduction_is_idempotent al).
        rewrite hl.
        set jal := (jt_reduce_exp al).
        have shallow_al : jt_depth al <=n. simpl in h. by lia.
        have h2: R_hype R al. exact: Ih al shallow_al.
        case Hjal: jal => [|jalm jalf|jall|jalr] //.
        - unfold R_hype in h2. rewrite/jal in Hjal. rewrite Hjal in h2.
          exact: R_alpha_0_hom al JEmpty h2.
        - unfold R_hype in h2. rewrite/jal in Hjal. rewrite Hjal in h2.
          have h3 : R (JLeft al) (JLeft (JNode jalm jalf)).
          - exact: R_alpha_0_hom al (JNode jalm jalf) h2.
          have h4: (jt_reduce_exp (JLeft (JNode jalm jalf))) = jt_reduce_exp jalm. 
          - have ht : jt_equiv' (JLeft (JNode jalm jalf)) jalm. exact: jt_equiv'_left_node jalm jalf.
            by apply/ jt_expression_beqP.
          rewrite h4.
          have h5: R (JLeft (JNode jalm jalf)) jalm. exact: R_alpha_0_rel jalm jalf.
          have h6: R jalm (jt_reduce_exp jalm).
          - have ht: jt_reduce_exp (JNode jalm jalf) = JNode jalm jalf ->  jt_reduce_exp jalm = jalm /\  jt_reduce_exp jalf = jalf. 
            - exact: jt_pass_down_reduction.1 jalm jalf.
            rewrite -Hjal in ht.
            by rewrite (ht (jt_reduction_is_idempotent al)).1.
          have h7: R (JLeft al) jalm. exact: R_trans (JLeft al) (JLeft (JNode jalm jalf)) jalm h3 h5.
          exact: R_trans (JLeft al) jalm (jt_reduce_exp jalm) h7 h6.
          rewrite - Hjal.
          have h4: jt_reduce_exp (JLeft jal) = (JLeft jal).
          - simpl. rewrite (jt_reduction_is_idempotent al).
            rewrite -/jal. by rewrite Hjal.
          rewrite h4.
          exact: R_alpha_0_hom al jal (Ih al shallow_al).
          rewrite - Hjal.
         have h4: jt_reduce_exp (JLeft jal) = (JLeft jal).
          - simpl. rewrite (jt_reduction_is_idempotent al).
            rewrite -/jal. by rewrite Hjal.
          rewrite h4.
          exact: R_alpha_0_hom al jal (Ih al shallow_al).
      - move => h.
        unfold R_hype.
        have hr: jt_reduce_exp (JRight ar) = jt_reduce_exp (JRight (jt_reduce_exp ar)).
        - simpl. by rewrite (jt_reduction_is_idempotent ar).
        rewrite hr.
        set jar := (jt_reduce_exp ar).
        have shallow_ar : jt_depth ar <=n. simpl in h. by lia.
        have h2: R_hype R ar. exact: Ih ar shallow_ar.
        case Hjar: jar => [|jarm jarf|jarl|jarr] //.
        - unfold R_hype in h2. rewrite/jar in Hjar. rewrite Hjar in h2.
          exact: R_alpha_1_hom ar JEmpty h2.
        - unfold R_hype in h2. rewrite/jar in Hjar. rewrite Hjar in h2.
          have h3 : R (JRight ar) (JRight (JNode jarm jarf)).
          - exact: R_alpha_1_hom ar (JNode jarm jarf) h2.
          have h4: (jt_reduce_exp (JRight (JNode jarm jarf))) = jt_reduce_exp jarf. 
          - have ht : jt_equiv' (JRight (JNode jarm jarf)) jarf. exact: jt_equiv'_right_node jarm jarf.
            by apply/ jt_expression_beqP.
          rewrite h4.
          have h5: R (JRight (JNode jarm jarf)) jarf. exact: R_alpha_1_rel jarm jarf.
          have h6: R jarf (jt_reduce_exp jarf).
          - have ht: jt_reduce_exp (JNode jarm jarf) = JNode jarm jarf ->  jt_reduce_exp jarm = jarm /\  jt_reduce_exp jarf = jarf. 
            - exact: jt_pass_down_reduction.1 jarm jarf.
            rewrite -Hjar in ht.
            by rewrite (ht (jt_reduction_is_idempotent ar)).2.
          have h7: R (JRight ar) jarf. exact: R_trans (JRight ar) (JRight (JNode jarm jarf)) jarf h3 h5.
          exact: R_trans (JRight ar) jarf (jt_reduce_exp jarf) h7 h6.
          rewrite- Hjar.
          have h4: jt_reduce_exp (JRight jar) = (JRight jar).
          - simpl. rewrite (jt_reduction_is_idempotent ar).
            rewrite -/jar. by rewrite Hjar.
          rewrite h4.
          exact: R_alpha_1_hom ar jar (Ih ar shallow_ar).
          rewrite- Hjar.
          have h4: jt_reduce_exp (JRight jar) = (JRight jar).
          - simpl. rewrite (jt_reduction_is_idempotent ar).
            rewrite -/jar. by rewrite Hjar.
          rewrite h4.
          exact: R_alpha_1_hom ar jar (Ih ar shallow_ar).
    have induct_conc: forall (n:nat) (a:jt_expression), (jt_depth a <= n) -> (R_hype R a).
    - induction n. exact: base_hype. exact: strong_induct.
    move => a.
    exact: induct_conc (jt_depth a) a (leqnn (jt_depth a)).
move => htemp.
unfold jt_equiv in htemp; simpl in htemp; unfold jt_equiv' in htemp.
have red_eq: (jt_reduce_exp x) = (jt_reduce_exp y).
- by apply/ jt_expression_beqP.
have R_2 : R (jt_reduce_exp x) (jt_reduce_exp y).
- rewrite red_eq. exact: R_refl (jt_reduce_exp y).
have h1: R x (jt_reduce_exp y). exact: R_trans x (jt_reduce_exp x) (jt_reduce_exp y) (R_red x) R_2.
exact: R_trans x (jt_reduce_exp y) y h1 (R_sym y (jt_reduce_exp y) (R_red y)).
Qed.

Fixpoint jt_hom_defined_by_gen (x: jt_elt): jt_expression -> jt_elt :=
  fun y => match y with
  | JEmpty => x
  | JLeft z => jt_alpha_0 ((jt_hom_defined_by_gen x) z)
  | JRight z => jt_alpha_1 ((jt_hom_defined_by_gen x) z)
  | JNode a b  => jt_lambda ((jt_hom_defined_by_gen x) a) ((jt_hom_defined_by_gen x) b)
  end.
Lemma jt_hom_defined_by_gen_is_hom_ker_contains_jt_equiv: 
forall (x:jt_elt) (y z:jt_expression),
jt_equiv y z -> ((jt_hom_defined_by_gen x) y = (jt_hom_defined_by_gen x) z).
Proof.
intro x.
set R: jt_expression -> jt_expression ->Prop := fun y z => ((jt_hom_defined_by_gen x) y = (jt_hom_defined_by_gen x) z).
apply jt_equiv_minimal.
by []. by [].
move => a b c h1 h2. by rewrite h1 //.
move => a b c d h1 h2. simpl. rewrite -h1. by rewrite -h2.
move => a b h1. simpl. by rewrite -h1.
move => a b h1. simpl. by rewrite -h1.
move => a. simpl. exact: free_jt_is_jt_algebra.1 (jt_hom_defined_by_gen x a).
move => a b. simpl. exact: free_jt_is_jt_algebra.2.1 (jt_hom_defined_by_gen x a) (jt_hom_defined_by_gen x b).
move => a b. simpl. exact: free_jt_is_jt_algebra.2.2 (jt_hom_defined_by_gen x a) (jt_hom_defined_by_gen x b).
Qed.
Definition jt_end_defined_by_gen (x: jt_elt): jt_elt -> jt_elt :=
fun y => (jt_hom_defined_by_gen x) (jt_rep y).
Lemma jt_end_defined_by_gen_is_end : forall (x: jt_elt), is_jt_endo (jt_end_defined_by_gen x).
Proof.
intro x. 
unfold is_jt_endo.
split. 2: split.
all: move => y.
3: move => z.
all: unfold jt_end_defined_by_gen; unfold jt_alpha_0; unfold quotient_pass_func.
all: by rewrite (jt_hom_defined_by_gen_is_hom_ker_contains_jt_equiv x (jt_rep (jt_proj _)) _ (jt_rep_proj_cancel_mod _)).
Qed.

Definition TV_elt_defined_by_gen (x: jt_elt): TV :=
exist _ (jt_end_defined_by_gen x) (jt_end_defined_by_gen_is_end x).
Lemma TV_elt_defined_by_gen_maps_gen: forall (x: jt_elt), TV_act (TV_elt_defined_by_gen x) jt_gen = x.
Proof.
intro x.
unfold TV_act. unfold TV_elt_defined_by_gen.
simpl. unfold jt_gen. unfold jt_end_defined_by_gen.
by rewrite (jt_rep_proj_cancel JEmpty).
Qed.

Definition TV_id := TV_elt_defined_by_gen (jt_gen).
Lemma TV_id_fixes_all: forall (x: jt_elt), TV_act TV_id x = x.
Proof.
intro x.
set true_id :jt_elt-> jt_elt := fun x=> x.
have h1 : is_jt_endo true_id. by [].
have h2: TV_act TV_id jt_gen =
       TV_act (exist is_jt_endo true_id h1) jt_gen ->
       TV_eq TV_id (exist is_jt_endo true_id h1).
exact: jt_hom_determined_by_gen TV_id (exist _ true_id h1).
have h3: TV_act TV_id jt_gen = jt_gen. exact: TV_elt_defined_by_gen_maps_gen jt_gen.
have h4: TV_act (exist is_jt_endo true_id h1) jt_gen = jt_gen. by [].
have h5: TV_eq TV_id (exist is_jt_endo true_id h1).
- rewrite h3 in h2. rewrite h4 in h2. by apply h2.
unfold TV_eq in h5. simpl in h5.
unfold TV_elt_defined_by_gen. simpl.
by rewrite h5.
Qed.


Lemma TV_is_monoid: 
(forall (f g h: TV), 
TV_eq (TV_comp (TV_comp h g) f) (TV_comp h (TV_comp g f))) /\
forall (f: TV), 
(TV_eq (TV_comp f TV_id) f) /\ (TV_eq (TV_comp TV_id f) f).
Proof.
split. exact: TV_is_semigroup.
move => f.
split.
- apply TV_action_determined.
  move => x.
  rewrite (TV_action_associates f TV_id x).
  by rewrite (TV_id_fixes_all x).
- apply TV_action_determined.
  move => x.
  rewrite (TV_action_associates TV_id f x).
  by rewrite (TV_id_fixes_all (TV_act f x)).
Qed.


Definition TV_are_inverse (f g: TV) := (TV_eq (TV_comp f g) TV_id) /\  (TV_eq (TV_comp g f) TV_id).
Definition V : Type := { pair :  TV * TV| TV_are_inverse (fst pair) (snd pair)}.
Definition V_TV_inclusion : V -> TV := fun f => fst (sval f).
Definition V_eq: V -> V -> Prop := fun f g => sval (fst (sval f)) = sval (fst (sval g)).  
Lemma V_TV_inclusion_injective: 
forall (f g: V), TV_eq (V_TV_inclusion f) (V_TV_inclusion g) -> V_eq f g.
Proof.
by [].
Qed.
Lemma TV_id_is_self_inverse: TV_are_inverse TV_id TV_id.
Proof.
unfold TV_are_inverse.
exact: TV_is_monoid.2 TV_id.
Qed.
Definition V_id : V := exist _ (TV_id, TV_id) TV_id_is_self_inverse.

Lemma inverse_reverses_order: 
forall (f g h k: TV), (TV_are_inverse f g) -> (TV_are_inverse h k)
-> TV_are_inverse (TV_comp f h) (TV_comp k g).
Proof.
move => f g h k fg_hype hk_hype.
unfold TV_are_inverse.
unfold TV_are_inverse in fg_hype.
unfold TV_are_inverse in hk_hype.
case fg_hype. case hk_hype.
move => hki khi fgi gfi.
split.
- apply jt_hom_determined_by_gen.
  rewrite (TV_action_associates (TV_comp f h) (TV_comp k g) jt_gen).
  rewrite (TV_action_associates k g jt_gen).
  rewrite (TV_action_associates f h (TV_act k (TV_act g jt_gen))).
  rewrite TV_id_fixes_all.
  rewrite -(TV_action_associates h k (TV_act g jt_gen)).
  rewrite (TV_eq_determines_action (TV_comp h k) TV_id (TV_act g jt_gen) hki).
  rewrite (TV_id_fixes_all (TV_act g jt_gen)).
  rewrite -(TV_action_associates f g jt_gen).
  rewrite (TV_eq_determines_action (TV_comp f g) TV_id jt_gen fgi).
  exact: (TV_id_fixes_all jt_gen).
- apply jt_hom_determined_by_gen.
  rewrite (TV_action_associates (TV_comp k g) (TV_comp f h) jt_gen).
  rewrite (TV_action_associates f h jt_gen).
  rewrite (TV_action_associates k g (TV_act f (TV_act h jt_gen))).
  rewrite TV_id_fixes_all.
  rewrite -(TV_action_associates g f (TV_act h jt_gen)).
  rewrite (TV_eq_determines_action (TV_comp g f) TV_id (TV_act h jt_gen) gfi).
  rewrite (TV_id_fixes_all (TV_act h jt_gen)).
  rewrite -(TV_action_associates k h jt_gen).
  rewrite (TV_eq_determines_action (TV_comp k h) TV_id jt_gen khi).
  exact: (TV_id_fixes_all jt_gen).
Qed.
Lemma swap_is_inverse: forall (f g: TV), (TV_are_inverse f g) -> (TV_are_inverse g f).
Proof.
move => h g fg_hype.
unfold TV_are_inverse in fg_hype.
split. exact fg_hype.2. exact fg_hype.1.
Qed.
Definition V_comp : V -> V -> V :=
  fun f g =>
    let: exist pf hf := f in
    let: exist pg hg := g in
    exist _ (TV_comp pf.1 pg.1, TV_comp pg.2 pf.2)
      (inverse_reverses_order pf.1 pf.2 pg.1 pg.2 hf hg).
Definition V_inv: V -> V.
Proof.
move => f.
case f => pf hf.
exact: exist _ (pf.2, pf.1) (swap_is_inverse pf.1 pf.2 hf).
Defined.
Definition V_act: V -> jt_elt -> jt_elt := fun f x => TV_act (V_TV_inclusion f) x.
Lemma V_action_associates: forall (f g: V) (x:jt_elt), 
V_act (V_comp f g) x = V_act f (V_act g x).
Proof.
unfold V_act.
move => f g x.
unfold V_TV_inclusion.
case f => pf hf. case g => pg hg.
simpl.
by unfold TV_act.
Qed.
Lemma V_action_determined: forall (f g: V), (forall (x:jt_elt), 
V_act f x = V_act g x) -> V_eq f g.
Proof.
move => f g hype.
unfold V_eq.
apply (@functional_extensionality_dep jt_elt (fun _ => jt_elt)).
by unfold TV_act in hype.
Qed.
Definition V_eq_determines_action (f g : V): forall (x:jt_elt), V_eq f g -> V_act f x = V_act g x.
Proof.
move => x heq.
unfold V_eq in heq; unfold V_act; unfold TV_act.
by rewrite heq.
Qed.


Lemma V_is_semigroup: 
forall (f g h: V), V_eq (V_comp (V_comp f g) h) (V_comp f (V_comp g h)).
Proof.
move => f g h.
case f => [pf hf].
case g => [pg hg].
case h => [ph hh].
simpl.
unfold V_eq.
by simpl.
Qed.
Lemma V_is_monoid: 
(forall (f g h: V), 
V_eq (V_comp (V_comp h g) f) (V_comp h (V_comp g f))) /\
forall (f: V), 
(V_eq (V_comp f V_id) f) /\ (V_eq (V_comp V_id f) f).
Proof.
split.
move => f g h. exact: V_is_semigroup h g f.
move => f.
case f => pf hf. 
unfold V_eq.
unfold V_comp.
simpl.
have h: forall x : jt_elt, TV_act TV_id x = x. exact: TV_id_fixes_all.
unfold TV_act in h.
unfold TV_id in h.
unfold TV_elt_defined_by_gen in h.
simpl in h.
split.
all: apply (@functional_extensionality_dep jt_elt (fun _ => jt_elt)).
all: intro x.
all: by rewrite h.
Qed.
Lemma V_is_group:
(forall (f g h: V), 
V_eq (V_comp (V_comp h g) f) (V_comp h (V_comp g f))) /\
(forall (f: V), 
(V_eq (V_comp f V_id) f) /\ (V_eq (V_comp V_id f) f)) /\
(forall (f: V), 
V_eq (V_comp f (V_inv f)) V_id /\ V_eq (V_comp (V_inv f) f) V_id).
Proof.
split. exact: V_is_monoid.1.
split. exact: V_is_monoid.2.
intro f.
case f => pf hf.
unfold V_eq.
simpl.
unfold TV_are_inverse in hf.
case hf.
move => h12 h21.
have fix12: forall (x:jt_elt), TV_act (TV_comp pf.1 pf.2) x = x.
- intro x.
  rewrite (TV_eq_determines_action (TV_comp pf.1 pf.2) TV_id x h12).
  exact: TV_id_fixes_all x.
have fix21: forall (x:jt_elt), TV_act (TV_comp pf.2 pf.1) x = x.
- intro x.
  rewrite (TV_eq_determines_action (TV_comp pf.2 pf.1) TV_id x h21).
  exact: TV_id_fixes_all x.
unfold TV_eq in hf.
unfold TV_act in fix12.
unfold TV_comp in fix12.
simpl in fix12.
unfold TV_act in fix21.
unfold TV_comp in fix21.
simpl in fix21.
have h: forall x : jt_elt, TV_act TV_id x = x. exact: TV_id_fixes_all.
unfold TV_act in h.
unfold TV_id in h.
unfold TV_elt_defined_by_gen in h.
simpl in h.
split.
all: apply (@functional_extensionality_dep jt_elt (fun _ => jt_elt)).
all: intro x.
rewrite (fix12 x).
by rewrite (h x).
rewrite (fix21 x).
by rewrite (h x).
Qed.


Create HintDb jt_expression_tools.
Hint Rewrite jt_rep_proj_cancel : jt_expression_tools.
Hint Rewrite jt_reduction_is_idempotent : jt_expression_tools.
Ltac jt_expression_simpl := autorewrite with jt_expression_tools.
Create HintDb jt_elt_tools.
Hint Rewrite jt_proj_rep_cancel : jt_elt_tools.
Hint Rewrite free_jt_is_jt_algebra.1 : jt_elt_tools.
Hint Rewrite free_jt_is_jt_algebra.2.1 : jt_elt_tools.
Hint Rewrite free_jt_is_jt_algebra.2.2 : jt_elt_tools.
Ltac jt_elt_simpl := autorewrite with jt_elt_tools.
Ltac jt_endo_simpl f hendo :=
  unfold is_jt_endo in hendo;
  repeat first [
    rewrite (hendo.1 _)
  | rewrite (hendo.2.1 _)
  | rewrite (hendo.2.2 _ _)
  ].


Definition x0_gen_map := (jt_lambda (jt_lambda (jt_alpha_0 jt_gen) (jt_alpha_0 (jt_alpha_1 jt_gen))) (jt_alpha_1 (jt_alpha_1 jt_gen))).
Definition TV_x0 : TV := TV_elt_defined_by_gen x0_gen_map.
Definition x0_inv_gen_map := (jt_lambda (jt_alpha_0 (jt_alpha_0 jt_gen)) (jt_lambda (jt_alpha_1 (jt_alpha_0 jt_gen)) (jt_alpha_1 jt_gen))).
Definition TV_x0_inv : TV := TV_elt_defined_by_gen x0_inv_gen_map.
Lemma TV_x0_x0_inv_are_inverses: TV_are_inverse TV_x0 TV_x0_inv.
Proof.
unfold TV_are_inverse.
set F := TV_x0; case F as [f hf] eqn:Fhy.
have Fact: TV_act F jt_gen = x0_gen_map.
exact: TV_elt_defined_by_gen_maps_gen x0_gen_map.
rewrite Fhy in Fact.
set G := TV_x0_inv; case G as [g hg] eqn:Ghy.
have Gact: TV_act G jt_gen = x0_inv_gen_map. 
exact: TV_elt_defined_by_gen_maps_gen x0_inv_gen_map.
rewrite Ghy in Gact.
simpl in Fact; simpl in Gact.
split.
all: apply jt_hom_determined_by_gen.
all: rewrite (TV_action_associates _ _ jt_gen).
all: rewrite (TV_id_fixes_all jt_gen); simpl.
rewrite Gact.
jt_endo_simpl f hf.
rewrite Fact.
unfold x0_gen_map; by jt_elt_simpl.
rewrite Fact.
jt_endo_simpl g hg.
rewrite Gact. 
unfold x0_inv_gen_map; by jt_elt_simpl.
Qed.
Definition x1_gen_map := jt_lambda (jt_alpha_0 jt_gen) (jt_lambda (jt_lambda (jt_alpha_0 (jt_alpha_1 jt_gen)) (jt_alpha_0 (jt_alpha_1 (jt_alpha_1 jt_gen)))) (jt_alpha_1 (jt_alpha_1 (jt_alpha_1 jt_gen)))).
Definition TV_x1 : TV := TV_elt_defined_by_gen x1_gen_map.
Definition x1_inv_gen_map := jt_lambda (jt_alpha_0 jt_gen) (jt_lambda (jt_alpha_0 (jt_alpha_0 (jt_alpha_1 jt_gen))) (jt_lambda (jt_alpha_1 (jt_alpha_0 (jt_alpha_1 jt_gen))) (jt_alpha_1 (jt_alpha_1 jt_gen)))).
Definition TV_x1_inv : TV := TV_elt_defined_by_gen x1_inv_gen_map.
Lemma TV_x1_x1_inv_are_inverses: TV_are_inverse TV_x1 TV_x1_inv.
Proof.
unfold TV_are_inverse.
set F := TV_x1; case F as [f hf] eqn:Fhy.
have Fact: TV_act F jt_gen = x1_gen_map.
exact: TV_elt_defined_by_gen_maps_gen x1_gen_map.
rewrite Fhy in Fact.
set G := TV_x1_inv; case G as [g hg] eqn:Ghy.
have Gact: TV_act G jt_gen = x1_inv_gen_map. 
exact: TV_elt_defined_by_gen_maps_gen x1_inv_gen_map.
rewrite Ghy in Gact.
simpl in Fact; simpl in Gact.
split.
all: apply jt_hom_determined_by_gen.
all: rewrite (TV_action_associates _ _ jt_gen).
all: rewrite (TV_id_fixes_all jt_gen); simpl.
rewrite Gact.
jt_endo_simpl f hf.
rewrite Fact.
unfold x1_gen_map; by jt_elt_simpl.
rewrite Fact.
jt_endo_simpl g hg.
rewrite Gact. 
unfold x1_inv_gen_map; by jt_elt_simpl.
Qed.
Definition V_x0 : V := exist _ (TV_x0, TV_x0_inv) TV_x0_x0_inv_are_inverses.
Definition V_x1 : V := exist _ (TV_x1, TV_x1_inv) TV_x1_x1_inv_are_inverses.



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
