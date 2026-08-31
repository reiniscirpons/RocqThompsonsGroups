Require Import ssreflect ssrbool ssrfun.
From HB Require Import structures.
Require Import ssreflect ssrfun ssrbool.
Require Import Lia.


(* Luna attempt at making the free jonsson tarski algeba. the node operator is usually called 
lambda in the literature and the child operators are usually called alpha_0 alpha_1. dont know if 
we should imitate that or stick to this. (might matter if/when we change arity) *)

Inductive jt_expression :=
| JEmpty: jt_expression
| JNode: jt_expression -> jt_expression -> jt_expression
| JLeft: jt_expression -> jt_expression
| JRight: jt_expression -> jt_expression.

Scheme Equality for jt_expression.

Fixpoint jt_depth (t : jt_expression) : nat :=
  match t with
  | JEmpty => 0
  | JNode a b =>
      S (max (jt_depth a) (jt_depth b))
  | JLeft x =>
      S (jt_depth x)
  | JRight x =>
      S (jt_depth x)
  end.

Lemma depth_zero_is_empty (x : jt_expression): jt_depth x = 0 -> x = JEmpty.
Proof.
intro h.
case xhype: x => [|xl xr|xl|xr].
by [].
rewrite xhype in h.
simpl in h.
by [].
rewrite xhype in h.
simpl in h.
by [].
rewrite xhype in h.
simpl in h.
by [].
Qed.

Lemma depth_at_most_zero_is_empty (x : jt_expression): (jt_depth x <= 0) -> x = JEmpty.
Proof.
intro h.
have h1: jt_depth x = 0.
by lia.
exact: depth_zero_is_empty h1.
Qed.

Lemma ref_leq: forall (n:nat), n<=n.
Proof.
by lia.
Qed.


(* Reflexivity *)
Lemma jt_expression_beq_refl : reflexive jt_expression_beq.
Proof.
  unfold reflexive.
  intro y.
  induction y.
  by [].
  simpl.
  apply/andP.
  all: by [].
Qed.


(* Symmetry *)
Lemma jt_expression_beq_sym : symmetric jt_expression_beq.
Proof.
  unfold symmetric.
  move => x y.
  Definition casenm (n m:nat) := forall (x y: jt_expression), (jt_depth x <= n) -> (jt_depth y <= m) -> jt_expression_beq x y = jt_expression_beq y x.
  have base: casenm 0 0.
  unfold casenm.
  move => a b.
  move => ha hb.
  rewrite (depth_at_most_zero_is_empty a ha).
  rewrite (depth_at_most_zero_is_empty b hb).
  by [].
  
  have inductm: forall (n m : nat), casenm n m -> casenm n (S m).
  move => n m hnm.
  unfold casenm.
  move => a b ha hb.
  case Hb: b=> [|bm bf|bl|br].
  have Htemp: jt_depth JEmpty <= m.
  simpl.
  by lia.
  exact: hnm a JEmpty ha Htemp.
  simpl.
  case Ha: a=> [|am af|al|ar].
  by [].
  simpl.
  have Htemp1: jt_depth bm <= m.
  rewrite Hb in hb.
  simpl in hb.
  by lia.
  have Htemp2: jt_depth bf <= m.
  rewrite Hb in hb.
  simpl in hb.
  by lia.
  have Htemp3: jt_depth am <= n.
  rewrite Ha in ha.
  simpl in ha.
  by lia.
  have Htemp4: jt_depth af <= n.
  rewrite Ha in ha.
  simpl in ha.
  by lia.
  rewrite (hnm am bm Htemp3 Htemp1).
  rewrite (hnm af bf Htemp4 Htemp2).
  by [].
  by [].
  by [].
  case Ha: a=> [|am af|al|ar].
  all: simpl.
  all: try by [].
  have Htemp1: jt_depth al <= n.
  rewrite Ha in ha.
  simpl in ha.
  by lia.
  have Htemp2: jt_depth bl <= m.
  rewrite Hb in hb.
  simpl in hb.
  by lia.
  rewrite (hnm al bl Htemp1 Htemp2).
  by [].
  case Ha: a=> [|am af|al|ar].
  all: simpl.
  all: try by [].
  have Htemp1: jt_depth ar <= n.
  rewrite Ha in ha.
  simpl in ha.
  by lia.
  have Htemp2: jt_depth br <= m.
  rewrite Hb in hb.
  simpl in hb.
  by lia.
  rewrite (hnm ar br Htemp1 Htemp2).
  by [].
  
  have inductn: forall (n m : nat), casenm n m -> casenm (S n) m.
  move => n m hnm.
  unfold casenm.
  move => a b ha hb.
  case Hb: b=> [|bm bf|bl|br].
  have Htemp: jt_depth JEmpty <= m.
  simpl.
  by lia.
  case Ha: a=> [|am af|al|ar].
  all: try simpl.
  all: try by [].
  case Ha: a=> [|am af|al|ar].
  all: try simpl.
  all: try by [].
  have Htemp1: jt_depth am <= n.
  rewrite Ha in ha.
  simpl in ha.
  by lia.
  have Htemp2: jt_depth bm <= m.
  rewrite Hb in hb.
  simpl in hb.
  by lia.
  rewrite (hnm am bm Htemp1 Htemp2).
  have Htemp3: jt_depth af <= n.
  rewrite Ha in ha.
  simpl in ha.
  by lia.
  have Htemp4: jt_depth bf <= m.
  rewrite Hb in hb.
  simpl in hb.
  by lia.
  rewrite (hnm af bf Htemp3 Htemp4).
  by [].
  case Ha: a=> [|am af|al|ar].
  5: case Ha: a=> [|am af|al|ar].
  all: try simpl.
  all: try by [].
  have Htemp1: jt_depth al <= n.
  rewrite Ha in ha.
  simpl in ha.
  by lia.
  have Htemp2: jt_depth bl <= m.
  rewrite Hb in hb.
  simpl in hb.
  by lia.
  rewrite (hnm al bl Htemp1 Htemp2).
  by [].
  have Htemp1: jt_depth ar <= n.
  rewrite Ha in ha.
  simpl in ha.
  by lia.
  have Htemp2: jt_depth br <= m.
  rewrite Hb in hb.
  simpl in hb.
  by lia.
  rewrite (hnm ar br Htemp1 Htemp2).
  by [].
  
  have induct_conc1: forall n m : nat, casenm n 0 -> casenm n m.
  intro n.
  induction m.
  by [].
  intro h.
  exact: (inductm n m) (IHm h).
  
  have induct_conc2: forall n m : nat, casenm n m.
  induction n.
  intro m.
  exact: induct_conc1 0 m base.
  intro m.
  exact: (inductn n m) (IHn m).
  exact: induct_conc2 (jt_depth x) (jt_depth y) x y (ref_leq (jt_depth x)) (ref_leq (jt_depth y)).
Qed.


(* Transitivity *)
Lemma jt_expression_beq_trans : transitive jt_expression_beq.
Proof.
  unfold transitive.
  move => y x z.
  Definition casenmr (n m r:nat) := forall (x y z: jt_expression), 
  (jt_depth x <= n) -> (jt_depth y <= m) -> (jt_depth z <= r) -> 
  jt_expression_beq x y -> jt_expression_beq y z -> jt_expression_beq x z.

  have base: casenmr 0 0 0.
  unfold casenmr.
  move => a b c.
  move => ha hb hc.
  rewrite (depth_at_most_zero_is_empty a ha).
  rewrite (depth_at_most_zero_is_empty b hb).
  rewrite (depth_at_most_zero_is_empty c hc).
  by [].
  
  have inductr: forall (n m r : nat), casenmr n m r -> casenmr n m (S r).
  move => n m r hnmr.
  unfold casenmr.
  move => a b c ha hb hc e1 e2.
  case Ha: a=> [|am af|al|ar].
  all: try case Hb: b=> [|bm bf|bl|br].
  all: try case Hc: c=> [|cm cf|cl|cr].
  all: try rewrite Ha in e1.
  all: try rewrite Ha in ha.
  all: try simpl in ha.
  all: try rewrite Hb in e1.
  all: try rewrite Hb in e2.
  all: try rewrite Hb in hb.
  all: try simpl in hb.
  all: try rewrite Hc in e2.
  all: try rewrite Hc in hc.
  all: try simpl in hc.
  all: try simpl.
  all: try by [].
  have Htemp1: jt_depth am <= n.
  simpl.
  by lia.
  have Htemp2: jt_depth bm <= m.
  simpl.
  by lia.
  have Htemp3: jt_depth cm <= r.
  simpl.
  by lia.
  have Htemp4: jt_depth af <= n.
  simpl.
  by lia.
  have Htemp5: jt_depth bf <= m.
  simpl.
  by lia.
  have Htemp6: jt_depth cf <= r.
  simpl.
  by lia.
  simpl in e1.
  simpl in e2.
  have gl: jt_expression_beq am cm.
  exact: hnmr am bm cm Htemp1 Htemp2 Htemp3 (andP e1).1 (andP e2).1.
  have gr: jt_expression_beq af cf.
  exact: hnmr af bf cf Htemp4 Htemp5 Htemp6 (andP e1).2 (andP e2).2.
  apply/andP.
  by [].
  
  have Htemp1: jt_depth al <= n.
  simpl.
  by lia.
  have Htemp2: jt_depth bl <= m.
  simpl.
  by lia.
  have Htemp3: jt_depth cl <= r.
  simpl.
  by lia.
  exact: hnmr al bl cl Htemp1 Htemp2 Htemp3 e1 e2.

  have Htemp1: jt_depth ar <= n.
  simpl.
  by lia.
  have Htemp2: jt_depth br <= m.
  simpl.
  by lia.
  have Htemp3: jt_depth cr <= r.
  simpl.
  by lia.
  exact: hnmr ar br cr Htemp1 Htemp2 Htemp3 e1 e2.

  have inductm: forall (n m r : nat), casenmr n m r -> casenmr n (S m) r.
  move => n m r hnmr.
  unfold casenmr.
  move => a b c ha hb hc e1 e2.
  case Ha: a=> [|am af|al|ar].
  all: try case Hb: b=> [|bm bf|bl|br].
  all: try case Hc: c=> [|cm cf|cl|cr].
  all: try rewrite Ha in e1.
  all: try rewrite Ha in ha.
  all: try simpl in ha.
  all: try rewrite Hb in e1.
  all: try rewrite Hb in e2.
  all: try rewrite Hb in hb.
  all: try simpl in hb.
  all: try rewrite Hc in e2.
  all: try rewrite Hc in hc.
  all: try simpl in hc.
  all: try simpl.
  all: try by [].
  have Htemp1: jt_depth am <= n.
  simpl.
  by lia.
  have Htemp2: jt_depth bm <= m.
  simpl.
  by lia.
  have Htemp3: jt_depth cm <= r.
  simpl.
  by lia.
  have Htemp4: jt_depth af <= n.
  simpl.
  by lia.
  have Htemp5: jt_depth bf <= m.
  simpl.
  by lia.
  have Htemp6: jt_depth cf <= r.
  simpl.
  by lia.
  simpl in e1.
  simpl in e2.
  have gl: jt_expression_beq am cm.
  exact: hnmr am bm cm Htemp1 Htemp2 Htemp3 (andP e1).1 (andP e2).1.
  have gr: jt_expression_beq af cf.
  exact: hnmr af bf cf Htemp4 Htemp5 Htemp6 (andP e1).2 (andP e2).2.
  apply/andP.
  by [].
  
  have Htemp1: jt_depth al <= n.
  simpl.
  by lia.
  have Htemp2: jt_depth bl <= m.
  simpl.
  by lia.
  have Htemp3: jt_depth cl <= r.
  simpl.
  by lia.
  exact: hnmr al bl cl Htemp1 Htemp2 Htemp3 e1 e2.

  have Htemp1: jt_depth ar <= n.
  simpl.
  by lia.
  have Htemp2: jt_depth br <= m.
  simpl.
  by lia.
  have Htemp3: jt_depth cr <= r.
  simpl.
  by lia.
  exact: hnmr ar br cr Htemp1 Htemp2 Htemp3 e1 e2.

  have inductn: forall (n m r : nat), casenmr n m r -> casenmr (S n) m r.
  move => n m r hnmr.
  unfold casenmr.
  move => a b c ha hb hc e1 e2.
  case Ha: a=> [|am af|al|ar].
  all: try case Hb: b=> [|bm bf|bl|br].
  all: try case Hc: c=> [|cm cf|cl|cr].
  all: try rewrite Ha in e1.
  all: try rewrite Ha in ha.
  all: try simpl in ha.
  all: try rewrite Hb in e1.
  all: try rewrite Hb in e2.
  all: try rewrite Hb in hb.
  all: try simpl in hb.
  all: try rewrite Hc in e2.
  all: try rewrite Hc in hc.
  all: try simpl in hc.
  all: try simpl.
  all: try by [].
  have Htemp1: jt_depth am <= n.
  simpl.
  by lia.
  have Htemp2: jt_depth bm <= m.
  simpl.
  by lia.
  have Htemp3: jt_depth cm <= r.
  simpl.
  by lia.
  have Htemp4: jt_depth af <= n.
  simpl.
  by lia.
  have Htemp5: jt_depth bf <= m.
  simpl.
  by lia.
  have Htemp6: jt_depth cf <= r.
  simpl.
  by lia.
  simpl in e1.
  simpl in e2.
  have gl: jt_expression_beq am cm.
  exact: hnmr am bm cm Htemp1 Htemp2 Htemp3 (andP e1).1 (andP e2).1.
  have gr: jt_expression_beq af cf.
  exact: hnmr af bf cf Htemp4 Htemp5 Htemp6 (andP e1).2 (andP e2).2.
  apply/andP.
  by [].
  
  have Htemp1: jt_depth al <= n.
  simpl.
  by lia.
  have Htemp2: jt_depth bl <= m.
  simpl.
  by lia.
  have Htemp3: jt_depth cl <= r.
  simpl.
  by lia.
  exact: hnmr al bl cl Htemp1 Htemp2 Htemp3 e1 e2.

  have Htemp1: jt_depth ar <= n.
  simpl.
  by lia.
  have Htemp2: jt_depth br <= m.
  simpl.
  by lia.
  have Htemp3: jt_depth cr <= r.
  simpl.
  by lia.
  exact: hnmr ar br cr Htemp1 Htemp2 Htemp3 e1 e2.
  
  have induct_conc1: forall n m r : nat, casenmr n m 0 -> casenmr n m r.
  move => n m.
  induction r.
  by [].
  intro h.
  exact: (inductr n m r) (IHr h).

  have induct_conc2: forall n m r : nat, casenmr n 0 0 -> casenmr n m r.
  move => n.
  induction m.
  move => r.
  exact: induct_conc1 n 0 r.
  move => r h.
  exact: (inductm n m r) (IHm r h).
  
  have induct_conc3: forall n m r: nat, casenmr n m r.
  induction n.
  move => m r.
  exact: induct_conc2 0 m r base.
  move => m r.
  exact: (inductn n m r) (IHn m r).
  exact: induct_conc3 (jt_depth x) (jt_depth y) (jt_depth z) x y z (ref_leq (jt_depth x)) (ref_leq (jt_depth y)) (ref_leq (jt_depth z)).
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
induction t.
all: try simpl.
by lia.
set jt1 := jt_reduce_exp t1.
set jt2 := jt_reduce_exp t2.
case h1: jt1 => [|jt1l jt1r|jt1l|jt1r].
try simpl.
Search (_ <= _ -> S _ <= S _).
apply le_n_S.
all: try move => j j0.
all: try move => j.
all: try move => j1.
all: try move => j2.
all: try set jtt := jt_reduce_exp t
all: try case jtt.
have htemp: jt_depth jt2 <= (jt_depth t2).
all: try by [].
all: try by lia.
all : simpl.
apply le_n_S.
3: apply le_n_S.
all: try rewrite -/jt1 in IHt1.
all: try rewrite -/jt2 in IHt2.
set m := jt_depth jt2.
case hm: m => [|m'].
have heq: S (Nat.max (jt_depth jt1l) (jt_depth jt1r)) = jt_depth jt1.
rewrite h1.
simpl.
by reflexivity.
rewrite heq.
by lia.
have heq: S (Nat.max (jt_depth jt1l) (jt_depth jt1r)) = jt_depth jt1.
rewrite h1.
simpl.
by reflexivity.
by lia.
case h2: jt2=> [|jt2l jt2r|jt2l|jt2r].
have Hl:  jt_depth (JNode (JLeft jt1l) JEmpty) = S( S (jt_depth jt1l)).
simpl.
by reflexivity.
rewrite Hl.
apply le_n_S.
have hl2: S(jt_depth jt1l) = jt_depth jt1.
rewrite h1.
simpl.
reflexivity.
all: try by lia.
all: try rewrite -h2.
all: try rewrite -h1.
all: try simpl.
all: try by lia.
set Htemp := jt_expression_beq jt1l jt2r.
case Htemp.
have hl2: S(jt_depth jt1l) = jt_depth jt1.
rewrite h1.
simpl.
reflexivity.
by lia.
simpl.
by lia.
set m := jt_depth jt2.
case Hm:m => [|m'].
have hr1: S(jt_depth jt1r) = jt_depth jt1.
rewrite h1.
simpl.
reflexivity.
by lia.
have Hl: S (Nat.max (jt_depth jt1r) m') <= Nat.max (jt_depth jt1) (jt_depth jt2).
rewrite PeanoNat.Nat.succ_max_distr.
have ht: S (jt_depth jt1r) = jt_depth jt1.
rewrite h1.
simpl.
reflexivity.
by lia.
by lia.
all: try set jtt:= jt_reduce_exp t.
all: try rewrite -/jtt in IHt.
all: case Htt: jtt=> [|jttl jttr|jttl|jttr].
all: simpl.
all: try by lia.
all: try apply le_n_S.
all: try have Hl: S (jt_depth jttl) <= jt_depth jtt.
all: try have Hr: S (jt_depth jttr) <= jt_depth jtt.
all: try rewrite Htt.
all: simpl.
all: try by lia.
Qed.

Fixpoint is_reduced (x : jt_expression) : bool :=
  match x with
  | JEmpty => true
  | JLeft y =>
      match y with
      | JEmpty => true
      | JLeft z => is_reduced y
      | JRight z => is_reduced y
      | JNode z a => false
      end
  | JRight y =>
      match y with
      | JEmpty => true
      | JLeft z => is_reduced y
      | JRight z => is_reduced y
      | JNode z a => false
      end
  | JNode y z =>
      match y, z with
      | JLeft a, JRight b =>
          negb (jt_expression_beq a b) &&
          is_reduced y &&
          is_reduced z
      | _, _ => is_reduced y && is_reduced z
      end
  end.


Lemma dont_reduce_reduced (x : jt_expression): is_reduced x -> jt_reduce_exp x = x.
Proof.
have inductversion: forall (n:nat), forall (x : jt_expression), jt_depth x <= n -> is_reduced x -> jt_reduce_exp x = x.
2: exact: inductversion (jt_depth x) x (ref_leq (jt_depth x)).

induction n.
intro y.
intro hy.
rewrite (depth_at_most_zero_is_empty y hy).
by [].
intro y.
intro h1.
intro h2.
case yhype: y => [|yl yr|yl|yr].
by [].
all: simpl.
rewrite yhype in h1.
simpl in h1.
apply le_S_n in h1.
have hyl:jt_depth yl <= n.
by lia.
have hyr:jt_depth yr <= n.
by lia.


have hyl2: jt_reduce_exp yl = yl.
rewrite yhype in h2.
have hyl3: is_reduced yl.
simpl in h2.
case ylhype: yl => [|yll ylr|yll|ylr].
by [].
rewrite ylhype in h2.
rewrite -ylhype in h2.
rewrite -ylhype.
exact (andP h2).1.
rewrite ylhype in h2.
rewrite -ylhype in h2.
rewrite -ylhype.
case yrhype: yr => [|yrl yrr|yrl|yrr].
all: try rewrite yrhype in h2.
all: try rewrite -yrhype in h2.
exact (andP h2).1.
exact (andP h2).1.
exact (andP h2).1.
exact: (andP ((andP h2).1)).2.
rewrite -ylhype.
rewrite ylhype in h2.
rewrite -ylhype in h2.
exact (andP h2).1.
exact: (IHn yl) hyl hyl3.
rewrite hyl2.

have hyr2: jt_reduce_exp yr = yr.
rewrite yhype in h2.
have hyr3: is_reduced yr.
simpl in h2.
case ylhype: yl => [|yll ylr|yll|ylr].
rewrite ylhype in h2.
rewrite -ylhype in h2.
exact (andP h2).2.
rewrite ylhype in h2.
rewrite -ylhype in h2.
exact (andP h2).2.
rewrite ylhype in h2.
rewrite -ylhype in h2.
case yrhype: yr => [|yrl yrr|yrl|yrr].
by [].
rewrite yrhype in h2.
rewrite -yrhype in h2.
rewrite -yrhype.
exact (andP h2).2.
rewrite yrhype in h2.
rewrite -yrhype in h2.
rewrite -yrhype.
exact (andP h2).2.
rewrite yrhype in h2.
rewrite -yrhype in h2.
rewrite -yrhype.
exact (andP h2).2.
rewrite ylhype in h2.
rewrite -ylhype in h2.
exact (andP h2).2.
exact: (IHn yr) hyr hyr3.
rewrite hyr2.

case  ylhype: yl => [|yll ylr|yll|ylr].
by [].
by [].
case yrhype: yr => [|yrl yrr|yrl|yrr].
by [].
by [].
by [].
set casehype := jt_expression_beq yll yrr.
case ch: casehype.
rewrite yhype in h2.
simpl in h2.
rewrite ylhype in h2.
rewrite yrhype in h2.
have hbad: ~~ jt_expression_beq yll yrr.
exact: (andP (andP h2).1).1.
have hbad2: jt_expression_beq yll yrr.
by [].
move/negPf in hbad.
move: hbad2.
rewrite hbad.
by [].
by [].
by [].

have hyl2: jt_reduce_exp yl = yl.
rewrite yhype in h2.
have hyl3: is_reduced yl.
simpl in h2.
case ylhype: yl => [|yll ylr|yll|ylr].
by [].
rewrite ylhype in h2.
by [].
rewrite ylhype in h2.
exact h2.
rewrite ylhype in h2.
exact h2.
rewrite yhype in h1.
simpl in h1.
apply le_S_n in h1.
exact: (IHn yl) h1 hyl3.
rewrite hyl2.

case ylhype: yl => [|yll ylr|yll|ylr].
by [].
rewrite yhype in h2.
simpl in h2.
rewrite ylhype in h2.
by [].
by [].
by [].


have hyr2: jt_reduce_exp yr = yr.
rewrite yhype in h2.
have hyr3: is_reduced yr.
simpl in h2.
case yrhype: yr => [|yrl yrr|yrl|yrr].
by [].
rewrite yrhype in h2.
by [].
rewrite yrhype in h2.
exact h2.
rewrite yrhype in h2.
exact h2.
rewrite yhype in h1.
simpl in h1.
apply le_S_n in h1.
exact: (IHn yr) h1 hyr3.
rewrite hyr2.

case yrhype: yr => [|yrl yrr|yrl|yrr].
by [].
rewrite yhype in h2.
simpl in h2.
rewrite yrhype in h2.
by [].
by [].
by [].
Qed.


Lemma inductive_reduced (a : jt_expression): ((jt_reduce_exp a = JEmpty) \/
(exists (b : jt_expression), jt_reduce_exp a = JLeft (jt_reduce_exp b)) \/
(exists (b : jt_expression), jt_reduce_exp a = JRight (jt_reduce_exp b)) \/
(exists (b c : jt_expression), jt_reduce_exp a = JNode (jt_reduce_exp b) (jt_reduce_exp c)))
/\ is_reduced (jt_reduce_exp a). 
Proof.
Definition conclusion1 (x : jt_expression):= (jt_reduce_exp x = JEmpty) \/
(exists (y : jt_expression), jt_reduce_exp x = JLeft (jt_reduce_exp y)) \/
(exists (y : jt_expression), jt_reduce_exp x = JRight (jt_reduce_exp y)) \/
(exists (y z : jt_expression), jt_reduce_exp x = JNode (jt_reduce_exp y) (jt_reduce_exp z)).

Definition conclusion2 (x : jt_expression):= is_reduced (jt_reduce_exp x).


Definition induct_claim_n (n: nat) := 
forall (x: jt_expression), (jt_depth (x) <= n) -> conclusion1 x /\ conclusion2 x.

have base: induct_claim_n 0.
unfold induct_claim_n.
intro x.
intro h.
split.
left.
rewrite (depth_at_most_zero_is_empty (x) h).
by [].
unfold conclusion2.
rewrite (depth_at_most_zero_is_empty (x) h).
by [].

have strong_induction_hype: forall (n: nat), induct_claim_n n -> induct_claim_n (S n).

2 :{
have all_claims: forall (n: nat), induct_claim_n n.
induction n.
exact: base.
exact: strong_induction_hype n IHn.
exact: all_claims (jt_depth ( a)) a (ref_leq (jt_depth ( a))).
}

unfold induct_claim_n.
intro n.
intro induct_hype.
intro x.
case Hx: x => [|xm xf|xl|xr].
split.
3:split.
5:split.
7:split.
by left.
by [].


(* conclusion1 node *)
unfold conclusion1.
simpl.
set xmj := jt_reduce_exp xm.
case Hxmj: xmj => [|xmjm xmjf|xmjl|xmjr].
right.
right.
right.
exists JEmpty.
exists xf.
by [].
rewrite -Hxmj.
right.
right.
right.
exists xm.
exists xf.
by [].

set xfj := jt_reduce_exp xf.
case Hxfj: xfj => [|xfjm xfjf|xfjl|xfjr].
right.
right.
right.
exists xm.
exists JEmpty.
rewrite -Hxmj.
by [].
rewrite -Hxfj.
rewrite -Hxmj.
right.
right.
right.
exists xm.
exists xf.
by [].
rewrite -Hxfj.
rewrite -Hxmj.
right.
right.
right.
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
have redtarg: is_reduced xmjl.
rewrite Hxmj in conc2xm.
simpl in conc2xm.
case Hxmjl: xmjl => [|xmjlm xmjlf|xmjll|xmjlr].
by [].
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

have HRxmj: is_reduced xmj.
exact: (induct_hype xm shallow_xm).2.
have HRxfj: is_reduced xfj.
exact: (induct_hype xf shallow_xf).2.

case Hxmj: xmj => [|xmjm xmjf|xmjl|xmjr].
simpl.
exact: HRxfj.
simpl.

case Hxmjm: xmjm => [|xmjmm xmjmf|xmjml|xmjmr].
have goal1: is_reduced JEmpty.
by [].
have goal2: is_reduced xmjf.
rewrite Hxmj in HRxmj.
simpl in HRxmj.
rewrite Hxmjm in HRxmj.
exact (andP HRxmj).2.
have goal3: is_reduced xfj.
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
have red_xljm: is_reduced xljm.
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
have red_xljmm: (is_reduced xljmm) /\ (is_reduced xljmf).
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

have red_xljml: is_reduced xljml.
rewrite Hxljm in red_xljm.
simpl in red_xljm.
case Hxljml: xljml => [|xljmlm xljmlf|xljmll|xljmlr].
by [].
all: try rewrite Hxljml in red_xljm.
by [].
by [].
by [].
have Heql:  (jt_reduce_exp xljml) = xljml.
exact: dont_reduce_reduced xljml red_xljml.
rewrite Heql.
by [].

right.
right.
left.
have red_xljmr: is_reduced xljmr.
rewrite Hxljm in red_xljm.
simpl in red_xljm.
case Hxljmr: xljmr => [|xljmrm xljmrf|xljmrl|xljmrr].
by [].
all: try rewrite Hxljmr in red_xljm.
by [].
by [].
by [].
have Heqr : (jt_reduce_exp xljmr) = xljmr.
exact: dont_reduce_reduced xljmr red_xljmr.
exists xljmr.
rewrite Heqr.
by [].
rewrite -Hxlj.
right.
left.
exists xl.
by [].
right.
left.
rewrite -Hxlj.
exists xl.
by [].

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
case Hxljm: xljm => [|xljmm xljmf|xljml|xljmr].
by [].
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
right.
right.
left.
exists JEmpty.
by [].
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
right.
right.
left.
exists xrj.
have Heq:  (jt_reduce_exp xrj) = xrj.
exact: dont_reduce_reduced xrj conc2cl.
rewrite Heq.
by [].
rewrite -/xrj.
intro h3.
case Hxrj: xrj => [|xrjm xrjf|xrjl|xrjr].
right.
right.
left.
exists JEmpty.
by [].
case h3.
intro h4.
case: h4 => [y hy].
rewrite hy in Hxrj.
by [].
intro h4.
case: h4 => [y h4].
case: h4 => [z h4].
rewrite Hxrj in h4.
case h2.
intro h5.
case h5 => [d hd].
rewrite -/xrj in hd.
rewrite Hxrj in hd.
by [].
rewrite -/xrj.
intro h6.
have red_xrjf: is_reduced xrjf.
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
right.
right.
right.
exists xrjfm.
exists xrjff.
have red_xrjfm: (is_reduced xrjfm) /\ (is_reduced xrjff).
rewrite Hxrjf in red_xrjf.
simpl in red_xrjf.
case Hxrjfm: xrjfm => [|xrjfmm xrjfmf|xrjfml|xrjfmr].
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
rewrite (dont_reduce_reduced xrjff red_xrjfm.2).
by [].
right.
left.
exists xrjfl.
have red_xrjfl: is_reduced xrjfl.
rewrite Hxrjf in red_xrjf.
simpl in red_xrjf.
case Hxrjfl: xrjfl => [|xrjflm xrjflf|xrjfll|xrjflr].
by [].
all: try rewrite Hxrjfl in red_xrjf.
all: try by [].
have Heqr:  (jt_reduce_exp xrjfl) = xrjfl.
exact: dont_reduce_reduced xrjfl red_xrjfl.
rewrite Heqr.
by [].
right.
right.
left.
have red_xrjfr: is_reduced xrjfr.
rewrite Hxrjf in red_xrjf.
simpl in red_xrjf.
case Hxrjfr: xrjfr => [|xrjfrm xrjfrf|xrjfrl|xrjfrr].
all: try rewrite Hxrjfr in red_xrjf.
all: try by [].
have Heqr : (jt_reduce_exp xrjfr) = xrjfr.
exact: dont_reduce_reduced xrjfr red_xrjfr.
exists xrjfr.
rewrite Heqr.
by [].
rewrite -Hxrj.
right.
right.
left.
exists xr.
by [].
right.
right.
left.
rewrite -Hxrj.
exists xr.
by [].

(* conclusion2 right *)
unfold conclusion2.
simpl.
set xrj:= jt_reduce_exp xr.
case Hxrj: xrj => [|xrjm xrjf|xrjl|xrjr].
by [].
have shallowxr : jt_depth xr <= n.
simpl in H.
by lia.
have conc1xr: conclusion1 xr.
exact: (induct_hype xr shallowxr).1.
have conc2cl: conclusion2 xr.
exact: (induct_hype xr shallowxr).2.
unfold conclusion2 in conc2cl.
rewrite -/xrj in conc2cl.
rewrite Hxrj in conc2cl.
simpl in conc2cl.
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

Lemma reduced_iff_is_reduction (x : jt_expression): 
(is_reduced x <-> 
jt_reduce_exp x = x)  /\ 
(is_reduced x <-> exists (y : jt_expression), jt_reduce_exp y = x).
Proof.
split.
split.
3: split.
exact: dont_reduce_reduced.
intro h.
rewrite -h.
exact: (inductive_reduced x).2.
intro h.
exists x.
exact: dont_reduce_reduced x h.
intro h.
case h=> [y hy].
rewrite -hy.
exact: (inductive_reduced y).2.
Qed.


Lemma jt_reduction_is_idempotent (x : jt_expression) : jt_reduce_exp (jt_reduce_exp x) = jt_reduce_exp x.
Proof.
have h: exists y, jt_reduce_exp y = jt_reduce_exp x.
exists x.
by [].
exact: (reduced_iff_is_reduction (jt_reduce_exp x)).1.1 ((reduced_iff_is_reduction (jt_reduce_exp x)).2.2 h).
Qed.



Definition jt_equiv : rel jt_expression := fun x y => jt_expression_beq (jt_reduce_exp x) (jt_reduce_exp y).

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

(* Luna: importing the following seems to break earlier proofs when we import them at the
start of the doc, this is why the import was delayed *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice.
From mathcomp Require Import seq fintype.


