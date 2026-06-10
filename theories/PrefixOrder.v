Require Import ssreflect ssrbool ssrfun.
From HB Require Import structures.
From mathcomp Require Import seq preorder eqtype choice.

Local Open Scope order_scope.

Reserved Notation "x <=^pre y" (at level 70, y at next level).
Reserved Notation "x >=^pre y" (at level 70, y at next level).
Reserved Notation "x <^pre y" (at level 70, y at next level).
Reserved Notation "x >^pre y" (at level 70, y at next level).
Reserved Notation "x <=^pre y :> T" (at level 70, y at next level).
Reserved Notation "x >=^pre y :> T" (at level 70, y at next level).
Reserved Notation "x <^pre y :> T" (at level 70, y at next level).
Reserved Notation "x >^pre y :> T" (at level 70, y at next level).
Reserved Notation "<=^pre y" (at level 35).
Reserved Notation ">=^pre y" (at level 35).
Reserved Notation "<^pre y" (at level 35).
Reserved Notation ">^pre y" (at level 35).
Reserved Notation "<=^pre y :> T" (at level 35, y at next level).
Reserved Notation ">=^pre y :> T" (at level 35, y at next level).
Reserved Notation "<^pre y :> T" (at level 35, y at next level).
Reserved Notation ">^pre y :> T" (at level 35, y at next level).
Reserved Notation "x >=<^pre y" (at level 70, no associativity).
Reserved Notation ">=<^pre x" (at level 35).
Reserved Notation ">=<^pre y :> T" (at level 35, y at next level).
Reserved Notation "x ><^pre y" (at level 70, no associativity).
Reserved Notation "><^pre x" (at level 35).
Reserved Notation "><^pre y :> T" (at level 35, y at next level).

Reserved Notation "x <=^pre y <=^pre z" (at level 70, y, z at next level).
Reserved Notation "x <^pre y <=^pre z" (at level 70, y, z at next level).
Reserved Notation "x <=^pre y <^pre z" (at level 70, y, z at next level).
Reserved Notation "x <^pre y <^pre z" (at level 70, y, z at next level).
Reserved Notation "x <=^pre y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  <=^pre  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <=^pre y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <=^pre  y '/'  ?=  'iff'  c  :> T ']'").

Reserved Notation "\bot^pre".

Import Order.


Fact seqprefix_display (disp : disp_t) : disp_t.
Proof. exact: disp. Qed.



Module Import SeqPrefixSyntax.

Notation "<=^pre%O" := (@le (seqprefix_display _ _) _) : function_scope.
Notation ">=^pre%O" := (@ge (seqprefix_display _ _) _) : function_scope.
Notation ">=^pre%O" := (@ge (seqprefix_display _ _) _) : function_scope.
Notation "<^pre%O" := (@lt (seqprefix_display _ _) _) : function_scope.
Notation ">^pre%O" := (@gt (seqprefix_display _ _) _) : function_scope.
Notation "<?=^pre%O" := (@leif (seqprefix_display _ _) _) : function_scope.
Notation ">=<^pre%O" := (@comparable (seqprefix_display _ _) _) : function_scope.
Notation "><^pre%O" := (fun x y => ~~ (@comparable (seqprefix_display _ _) _ x y)) :
  function_scope.

Notation "<=^pre y" := (>=^pre%O y) : order_scope.
Notation "<=^pre y :> T" := (<=^pre (y : T)) (only parsing) : order_scope.
Notation ">=^pre y"  := (<=^pre%O y) : order_scope.
Notation ">=^pre y :> T" := (>=^pre (y : T)) (only parsing) : order_scope.

Notation "<^pre y" := (>^pre%O y) : order_scope.
Notation "<^pre y :> T" := (<^pre (y : T)) (only parsing) : order_scope.
Notation ">^pre y" := (<^pre%O y) : order_scope.
Notation ">^pre y :> T" := (>^pre (y : T)) (only parsing) : order_scope.

Notation "x <=^pre y" := (<=^pre%O x y) : order_scope.
Notation "x <=^pre y :> T" := ((x : T) <=^pre (y : T)) (only parsing) : order_scope.
Notation "x >=^pre y" := (y <=^pre x) (only parsing) : order_scope.
Notation "x >=^pre y :> T" := ((x : T) >=^pre (y : T)) (only parsing) : order_scope.

Notation "x <^pre y"  := (<^pre%O x y) : order_scope.
Notation "x <^pre y :> T" := ((x : T) <^pre (y : T)) (only parsing) : order_scope.
Notation "x >^pre y"  := (y <^pre x) (only parsing) : order_scope.
Notation "x >^pre y :> T" := ((x : T) >^pre (y : T)) (only parsing) : order_scope.

Notation "x <=^pre y <=^pre z" := ((x <=^pre y) && (y <=^pre z)) : order_scope.
Notation "x <^pre y <=^pre z" := ((x <^pre y) && (y <=^pre z)) : order_scope.
Notation "x <=^pre y <^pre z" := ((x <=^pre y) && (y <^pre z)) : order_scope.
Notation "x <^pre y <^pre z" := ((x <^pre y) && (y <^pre z)) : order_scope.

Notation "x <=^pre y ?= 'iff' C" := (<?=^pre%O x y C) : order_scope.
Notation "x <=^pre y ?= 'iff' C :> T" := ((x : T) <=^pre (y : T) ?= iff C)
  (only parsing) : order_scope.

Notation ">=<^pre y" := [pred x | >=<^pre%O x y] : order_scope.
Notation ">=<^pre y :> T" := (>=<^pre (y : T)) (only parsing) : order_scope.
Notation "x >=<^pre y" := (>=<^pre%O x y) : order_scope.

Notation "><^pre y" := [pred x | ~~ (>=<^pre%O x y)] : order_scope.
Notation "><^pre y :> T" := (><^pre (y : T)) (only parsing) : order_scope.
Notation "x ><^pre y" := (~~ (><^pre%O x y)) : order_scope.

End SeqPrefixSyntax.

Module SeqPrefixOrder.
Section SeqPrefixOrder.

Definition type (disp : Order.disp_t) T := seq T.
Definition type_ (disp : Order.disp_t) (T : preorderType disp) :=
  type (seqprefix_display disp) T.

Context {disp disp' : Order.disp_t}.

Local Notation seq := (type disp').

#[export] HB.instance Definition _ (T : eqType) := Equality.on (seq T).
#[export] HB.instance Definition _ (T : choiceType) := Choice.on (seq T).
#[export] HB.instance Definition _ (T : countType) := Countable.on (seq T).

Section Preorder.
Context (T : preorderType disp).
Implicit Types (s : seq T).

Definition le s1 s2 := prefix s1 s2.
Fixpoint lt s1 s2 :=
  match s1, s2 with
  | [::], _ :: _ => true
  | x :: s1', y :: s2' => (x == y) && lt s1' s2'
  | _, _ => false
  end.


Fact refl: reflexive le.
Proof. by exact: prefix_refl. Qed.

Fact trans: transitive le.
Proof. by exact: prefix_trans. Qed.

Lemma lt_le_def s1 s2 : lt s1 s2 = le s1 s2 && ~~ le s2 s1.
Proof.
  elim: s1 s2 => [|x1 s1 H] [|x2 s2] // /=.
  rewrite H eq_sym; by case: (x2 == x1).
Qed.

#[export]
HB.instance Definition _ := isPreorder.Build disp' (seq T) lt_le_def refl trans.

Lemma leEseqprefix s1 s2 :
   s1 <= s2 = if s1 isn't x1 :: s1' then true else
              if s2 isn't x2 :: s2' then false else
              (x1 == x2) && (s1' <= s2' :> seq T).
Proof. by case: s1; case: s2. Qed.

Lemma ltEseqprefixlt s1 s2 :
   s1 < s2 = if s2 isn't x2 :: s2' then false else
              if s1 isn't x1 :: s1' then true else
              (x1 == x2) && (s1' < s2' :> seq T).
Proof. by case: s1; case: s2. Qed.

Lemma seqprefix0s s : [::] <= s :> seq T. Proof. by exact: prefix0s. Qed.

Lemma seqprefixs0 s : (s <= [::]) = (s == [::]).
Proof. by case: s. Qed.

Lemma seqprefixlt0s s : ([::] < s :> seq T) = (s != [::]). Proof. by case: s. Qed.

Lemma seqprefixlts0 s : (s < [::]) = false. Proof. by case: s. Qed.

Lemma seqprefix_cons x1 s1 x2 s2 :
  (x1 :: s1 <= x2 :: s2 :> seq T) = (x1 == x2) && (s1 <= s2).
Proof. exact: prefix_cons. Qed.

Lemma seqprefixlt_cons x1 s1 x2 s2 :
  (x1 :: s1 < x2 :: s2 :> seq T) = (x1 == x2) && (s1 < s2).
Proof. done. Qed.

Lemma seqprefix_eqhead x s1 y s2 : x :: s1 <= y :: s2 :> seq T -> x == y.
Proof. by rewrite seqprefix_cons => /andP[]. Qed.

Lemma seqprefixlt_eqhead x s1 y s2 : x :: s1 < y :: s2 :> seq T -> x == y.
Proof. by rewrite seqprefixlt_cons => /andP[]. Qed.

Lemma eqhead_seqprefixE (x : T) s1 s2 : (x :: s1 <= x :: s2 :> seq _) = (s1 <= s2).
Proof. by rewrite seqprefix_cons eq_refl. Qed.

Lemma eqhead_seqprefixltE (x : T) s1 s2 : (x :: s1 < x :: s2 :> seq _) = (s1 < s2).
Proof. by rewrite seqprefixlt_cons eq_refl. Qed.

Lemma seqprefix_comparable_cons: forall x1 s1 x2 s2,
  ((x1::s1: seq T) >=< (x2::s2: seq T)) =
    (x1 == x2) && (s1 >=< s2).
Proof.
  move => x1 s1 x2 s2.
  rewrite !/(_ >=< _) !seqprefix_cons eq_sym.
  by case: (x2 == x1).
Qed.

#[export]
HB.instance Definition _ := hasBottom.Build _ (seq T) seqprefix0s.

End Preorder.

Lemma sub_seqprefix_lexi d (T : preorderType disp) :
   subrel (<=%O : rel (seq T)) (<=%O : rel (seqlexi_with d T)).
Proof.
elim=> [|x1 s1 ihs1] [|x2 s2]//=; rewrite seqprefix_cons lexi_cons /=.
move => /andP [/eqP -> /ihs1 ->];
by rewrite implybT andbC /=.
Qed.

End SeqPrefixOrder.

Module Exports.

HB.reexport SeqPrefixOrder.

Notation seqprefix_with := type.
Notation seqprefix := type_.

Definition leEseqprefix := @leEseqprefix.
Definition seqprefix0s := @seqprefix0s.
Definition seqprefixs0 := @seqprefixs0.
Definition seqprefix_cons := @seqprefix_cons.
Definition seqprefix_eqhead := @seqprefix_eqhead.
Definition eqhead_seqprefixE := @eqhead_seqprefixE.

Definition ltEseqprefixlt := @ltEseqprefixlt.
Definition seqprefixlt0s := @seqprefixlt0s.
Definition seqprefixlts0 := @seqprefixlts0.
Definition seqprefixlt_cons := @seqprefixlt_cons.
Definition seqprefixlt_lehead := @seqprefixlt_eqhead.
Definition eqhead_seqprefixltE := @eqhead_seqprefixltE.

Definition sub_seqprefix_lexi := @sub_seqprefix_lexi.
Definition seqprefix_comparable_cons := @seqprefix_comparable_cons.

End Exports.
End SeqPrefixOrder.
HB.export SeqPrefixOrder.Exports.

Module DefaultSeqPrefixOrder.
Section DefaultSeqPrefixOrder.
Context {disp : disp_t}.

Notation seqprefix := (seqprefix_with (seqprefix_display disp)).

HB.instance Definition _ (T : preorderType disp) :=
  Preorder.copy (seq T) (seqprefix T).
HB.instance Definition _ (T : preorderType disp) :=
  BPreorder.copy (seq T) (seqprefix T).

End DefaultSeqPrefixOrder.
End DefaultSeqPrefixOrder.

Import BoolOrder.
Definition binary_word := seqprefix bool_display bool.
