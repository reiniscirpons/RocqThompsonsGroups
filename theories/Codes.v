Require Import ssreflect ssrbool ssrfun.
From HB Require Import structures.
From mathcomp Require Import
  ssrnat eqtype choice div seq preorder order path
  zify.
From Thompson Require Import PrefixOrder.

Import Order.PreorderTheory.
Import Order.POrderTheory.

Open Scope order_scope.

(*
  Initially:
    Binary 1-rooted 
    F, T, V groups
  Milestone:
    F is finitely generated
*)

(* NOTE(reiniscirpons): binary_word is now defined in
   PrefixOrder.v, where we also give them the prefix order.
   Hence we can now use the following notations:
   x <= y <-> x is a prefix of y
   x < y <-> x is a strict prefix of y
   x >=<y <-> x and y are comparable
   x >< y <-> x and y are incomparable
   *)

(* NOTE(reiniscirpons):
   We require a binary_code to be a set. We implement
   this by requiring that a binary code be sorted with
   respect to the lexicographic order on sequences.
   Since we use the non-strict order <=%O below, it
   follows that we actually allow for multisets, which
   may be useful in the future. *)
Definition binary_code (code: seq binary_word) :=
  sorted (<=%O) (code: seq (seqlexi bool)).

(* TODO(reiniscirpons): Explicitly mention prefix codes are finite
   in this development *)
(*Fixpoint prefix_code (code: binary_code): bool :=*)
(*  match code with*)
(*  | nil => true*)
(*  | word::code' =>*)
(*    (all (fun word' => word' >< word) code') &&*)
(*    (prefix_code code')*)
(*  end.*)

Definition prefix_code (code: seq binary_word): bool :=
  binary_code code &&
  pairwise (fun x y => (x >< y)) code.


(* The following lemma establishes that the `prefix_code` function
   coincides with the mathematical definition of a prefix code.
   Note we implement the set condition by requiring that it
   is strictly sorted with respect to the lexicographic order. *)
Lemma prefix_codeP: forall code,
  reflect
    (sorted (<%O) (code: seq (seqlexi bool)) /\
      (forall (word1 word2: binary_word),
        word1 \in code ->
        word2 \in code ->
        word1 >=< word2 ->
        word1 = word2))
    (prefix_code code).
Proof.
  move => code; apply (iffP idP) => /= [|[]].
  - rewrite /prefix_code =>
      /andP [/sortedP Hsort Hcomp]; split.
  -- apply /(sortedP [::]) => i Hi.
     move: (Hsort [::] i Hi).
     rewrite le_eqVlt => /orP [/eqP H|//].
     exfalso.
     enough (Hfalso: nth [::] code i >< nth [::] code i.+1);
       first by move/incomparable_eqF/eqP: Hfalso; rewrite H.
     move/pairwiseP in Hcomp.
     apply Hcomp => [|//|//];
       (* TODO(reiniscirpons): Why does by lia fail here !?*)
     enough (Hi': (i < size code)%N) => [//|].
     by apply ltn_trans with i.+1.

  - elim: code Hcomp {Hsort} => /=
      [//|word code IH /andP [/allP Hcomp /IH {IH} H] word1 word2].
  -- rewrite !in_cons => /orP [/eqP ->|H1] /orP [/eqP ->|H2] //.
  --- by move: H2 => /Hcomp /negP.
  --- by move: H1 => /Hcomp /negP; rewrite comparable_sym.
  --- by move => H3; apply H.
  - elim: code => [//|word code IH Hsort Hcomp].
    apply /andP; split.
  -- apply /(sortedP [::]) => i Hi.
     rewrite le_eqVlt; apply /orP; right.
     move/sortedP in Hsort.
     by apply Hsort.

  -- enough (H: prefix_code code).
  --- move/andP: H => /= [_ ->].
      apply /andP; split => [|//].
      apply/allP => x Hx; apply /negP => Hwx.
      enough (Hfalso: word = x).
  ---- move: Hsort; rewrite sorted_pairwise /=;
         last by exact: lt_trans.
       move/andP => [/allP H];
       by move: (H x Hx); rewrite Hfalso ltxx.
  ---- apply Hcomp => [||//];
       rewrite in_cons; apply/orP.
  ----- by left.
  ----- by right.
  -- apply IH;
       first by move/(drop_sorted 1): Hsort => /=; rewrite drop0.
     move => word1 word2 H1 H2 H12; apply Hcomp => [||//];
     by rewrite in_cons; apply/orP; right.
Qed.

Definition prepend (letter: bool) (code: seq binary_word):
  seq binary_word :=
    [seq letter::word | word <- code].

Lemma prepend_cons: forall letter word code,
  prepend letter (word::code) = (letter::word)::(prepend letter code).
Proof. done. Qed.

Lemma binary_code_prepend: forall letter code,
  binary_code code -> binary_code (prepend letter code).
Proof.
  move => letter; elim =>
    [//|word1 [//|word2 code]] /= IH /andP [H /IH ->].
  by rewrite eqhead_lexiE H.
Qed.

Lemma prefix_code_prepend: forall letter code,
  prefix_code code -> prefix_code (prepend letter code).
Proof.
  move => letter code;
  rewrite /prefix_code => /andP [/(binary_code_prepend letter)] -> /=.
  elim: code => [//|word code /= IH /andP [/allP H /IH ->]].
  apply /andP; split => [|//].
  apply /allP => x /mapP [y /H Hy ->].
  by rewrite seqprefix_comparable_cons eq_refl.
Qed.

Lemma prepend_uniq: forall (letter: bool) (code: seq binary_word),
  uniq code -> uniq (prepend letter code).
Proof.
  move => letter; elim => [//|word code IH /= /andP [Hw /IH ->]].
  apply /andP; split => [|//].
  apply /memPn => word' /mapP [word'' Hw'' ->].
  apply /eqP; case => H; rewrite H in Hw''.
  by move/negP: Hw.
Qed.

Lemma binary_code_behead: forall {word code},
  binary_code (word::code) -> binary_code code.
Proof.
  by move => word1 [//|word2 code /= /andP [_ ->]].
Qed.

Lemma prefix_code_behead: forall word code,
  prefix_code (word::code) -> prefix_code code.
Proof.
  rewrite /prefix_code.
  by move => word code /= /andP
    [/binary_code_behead -> /= /andP [_ ->]].
Qed.

Lemma prefix_code_cons_nil: forall code,
  prefix_code ([::]::code) -> code = [::].
Proof.
  rewrite /prefix_code.
  case => [//|word code] /= /andP [_ /andP [/andP [H _ _]]].
  exfalso.
  by rewrite seqprefix_comparable0s in H.
Qed.

Inductive binary_tree :=
| Empty: binary_tree
| Node: binary_tree -> binary_tree -> binary_tree.

Scheme Equality for binary_tree.

Lemma binary_tree_eqP: forall (tree1 tree2: binary_tree),
  reflect (tree1 = tree2) (binary_tree_beq tree1 tree2).
Proof.
  move => tree1 tree2.
  apply (iffP idP).
  - elim: tree1 tree2 => [ | l Hl r Hr]; case => //.
    by move => l2 r2 /= /andP [] /Hl <- /Hr <-.
  - move => <-; elim: tree1 => [//|l Hl r Hr /=].
    by rewrite Hl Hr. 
Qed.

HB.instance Definition _ :=
  hasDecEq.Build binary_tree binary_tree_eqP.

Fixpoint binary_tree_merge (tree1 tree2: binary_tree): binary_tree :=
  match tree1, tree2 with
  | Node l1 r1, Node l2 r2 =>
    Node (binary_tree_merge l1 l2) (binary_tree_merge r1 r2)
  | Empty, _ => tree2
  | _, Empty => tree1
  end.

Lemma binary_tree_merget0: forall tree,
  binary_tree_merge tree Empty = tree.
Proof. by case. Qed.

Lemma binary_tree_merge0t: forall tree,
  binary_tree_merge Empty tree = tree.
Proof. done. Qed.

Lemma binary_tree_mergeA: associative binary_tree_merge.
Proof.
  elim => [|l Hl r Hr]; case => [|l2 r2]; case => [|l3 r3] //=.
  by rewrite Hr Hl.
Qed.

Lemma binary_tree_mergeC: commutative binary_tree_merge.
Proof.
  elim => [|l Hl r Hr]; case => [|l2 r2] //=.
  by rewrite Hr Hl.
Qed.

Lemma binary_tree_mergeb: idempotent_op binary_tree_merge.
Proof.
  elim => [|l Hl r Hr] //=.
  by rewrite Hr Hl.
Qed.

Definition Leaf := Node Empty Empty.
Definition Caret := Node Leaf Leaf.

Fixpoint linear_tree (word: binary_word): binary_tree :=
  match word with
  | nil => Leaf
  | false::word' => Node (linear_tree word') Empty
  | true::word' => Node Empty (linear_tree word')
  end.

Lemma linear_tree_non_empty: forall word,
  linear_tree word != Empty.
Proof.
  by elim => [//|]; case.
Qed.

Definition add_word
  (word: binary_word) (tree: binary_tree): binary_tree :=
    binary_tree_merge (linear_tree word) tree.

Arguments add_word / _ _.

Lemma add_word0t: forall tree,
  tree != Empty -> add_word [::] tree = tree.
Proof.
  by case.
Qed.

Fixpoint tree_of_code (code: seq binary_word): binary_tree :=
  match code with
  | nil => Empty
  | word::code' => add_word word (tree_of_code code')
  end.

Lemma tree_of_code_cat: forall code1 code2,
  tree_of_code (code1 ++ code2) =
    binary_tree_merge (tree_of_code code1) (tree_of_code code2).
Proof.
  elim => [//|word code1 IH code2 /=].
  by rewrite -binary_tree_mergeA IH.
Qed.

Lemma tree_of_code_prepend: forall letter code,
  tree_of_code (prepend letter code) =
    if code == [::] then
      Empty
    else if letter then
      Node Empty (tree_of_code code)
    else
      Node (tree_of_code code) Empty.
Proof.
  move => letter code; case: ifP => [/eqP -> //|].
  elim: code => [//|word code]; case letter => /=;
  case: code => [_ _ |word' code /= IH _].
    1,3: by rewrite binary_tree_merget0.
  1,2: by rewrite IH.
Qed.

Lemma tree_of_code_empty: forall code,
  reflect (tree_of_code code == Empty) (code == [::]).
Proof.
  case => /= [|word code]; apply (iffP idP) => //.
  - case: word => [|[] word] /=;
    by case: (tree_of_code code).
Qed.

Fixpoint code_of_tree (tree: binary_tree): seq binary_word :=
  match tree with
  | Empty => nil
  | Node l r =>
    if (tree == Leaf) then
      [:: [::]]
    else
      (prepend false (code_of_tree l)) ++
      (prepend true (code_of_tree r))
  end.

Lemma code_of_tree_linear_tree: forall word,
  code_of_tree (linear_tree word) = [:: word].
Proof.
  elim => [//|[] word /=];
  by case: (linear_tree word) => [//|l r ->].
Qed.

Lemma binary_code_code_of_tree: forall tree,
  binary_code (code_of_tree tree).
Proof.
  elim => [//|l Hl r Hr /=];
  case: ifP => [//|Hleaf].
  move: Hr; case: (code_of_tree r) => [_ /=|word code];
    first by rewrite cats0; apply binary_code_prepend.
  rewrite /binary_code prepend_cons sorted_cat_cons => Hr.
  apply /andP; split.
  - move/sortedP in Hl.
    apply/(sortedP [::]) => i; rewrite !nth_rcons !size_rcons !size_map.
    case: ifP => Hi; case: ifP => Hi' Hi''.
  -- rewrite !(nth_map [::]) => [|//|//].
     by move/(Hl [::] i): Hi'; rewrite eqhead_lexiE.
  -- case: ifP => [_|]; last by lia.
     by rewrite (nth_map [::]).
  -- by lia.
  -- by lia.
  - move: (binary_code_prepend true (word::code) Hr).
    by rewrite prepend_cons.
Qed.

Lemma prefix_code_code_of_tree: forall tree,
  prefix_code (code_of_tree tree).
Proof.
  move => tree; rewrite /prefix_code binary_code_code_of_tree /=.
  elim: tree => [//|l Hl r Hr /=].
  case: ifP => [//|_].
  rewrite pairwise_cat.
  apply /andP; split;
    first by apply /allrelP => x y /mapP [x' _ ->] /mapP [y' _ ->].
  apply/andP; split; apply/(pairwiseP [::]) => i j;
  rewrite !size_map => Hi Hj Hij; rewrite !(nth_map [::]) => [|//|//];
  rewrite seqprefix_comparable_cons eq_refl /=;
  move/(pairwiseP [::]) in Hl;
  move/(pairwiseP [::]) in Hr.
  - by apply Hl.
  - by apply Hr.
Qed.

Lemma tree_of_codeK: forall tree,
  tree_of_code (code_of_tree tree) = tree.
Proof.
  elim => [//|l Hl r Hr] /=.
  case: ifP => [/eqP [-> ->] //|H /=].
  rewrite tree_of_code_cat !tree_of_code_prepend /=.
  move: Hl Hr H;
  case: ifP => [/eqP -> /= <-|_ ->];
  case: ifP => [/eqP -> /= <-|_ ->] //= _.
  by rewrite binary_tree_merget0.
Qed.

Definition child_code (letter: bool) (code: seq binary_word):
  seq binary_word :=
    filter (fun x => ohead x == Some letter) code.

Lemma binary_code_child_code: forall letter code,
  binary_code code -> binary_code (child_code letter code).
Proof.
  move => letter code H.
  rewrite /binary_code sorted_filter => [//||//].
  by exact le_trans.
Qed.

Lemma prefix_code_child_code: forall letter code,
  prefix_code code -> prefix_code (child_code letter code).
Proof.
  move => letter code.
  rewrite /prefix_code => /andP [/binary_code_child_code -> /= H].
  by apply /pairwise_filter.
Qed.

(* TODO(reiniscirpons): lemma about reconstructing binary
   code from its children. *)

Lemma code_of_treeK: forall code,
  prefix_code code ->
  code_of_tree (tree_of_code code) = code.
Proof.
  (*elim => [//|[|letter word] code IH];*)
  (*  first by move/prefix_code_cons_nil => ->.*)
  (*move => /=.*)
  (*case: letter => Hword /= /IH;*)
  (*case: (tree_of_code code) => /=.*)
  (*=> [<- /=|l r].*)
  (*1,3: rewrite code_of_tree_linear_tree /=;*)
  (*     move: (linear_tree_non_empty word);*)
  (*     by case: (linear_tree word) => [//|l r _].*)
  (*- move => /=.*)
Admitted.

Fixpoint any_leaf (tree:binary_tree): option binary_word :=
  match tree with
  | Empty => None
  | Node l r =>
    if any_leaf l is Some w then
      Some (true::w)
    else if any_leaf r is Some w then
      Some (false::w)
    else
      Some nil
  end.

Lemma any_leaf_none: forall tree,
  reflect (any_leaf tree == None) (tree == Empty).
Proof.
  move => tree; apply: (iffP idP) => [/eqP -> //|/eqP].
  elim: tree => [//|l Hl r Hr /=].
  case Hl': (any_leaf l) => [//|].
  by case Hr': (any_leaf r).
Qed.

Lemma any_leaf_in_code_of_tree: forall tree word,
  any_leaf tree = Some word -> word \in code_of_tree tree.
Proof.
  elim => [//|l Hl r Hr /=].
  case Hll: (any_leaf l) => [word'|].
  - move => word [<-] /=.
    have: (any_leaf l != None) => [|]; first by rewrite Hll.
    move => /negP /any_leaf_none; case: l {Hl Hll} => [//| ll lr /=].
(* TODO: This sucks :( *)
Admitted.

Fixpoint follow_word (tree: binary_tree) (word: binary_word):
  option binary_word :=
    match tree, word with
    | Empty, _ => None
    | _, nil => any_leaf tree
    | Node l _, false::word' =>
      match follow_word l word' with
      | None => Some nil
      | Some lw' => Some (false::lw')
      end
    | Node _ r, true::word' =>
      match follow_word r word' with
      | None => Some nil
      | Some rw' => Some (true::rw')
      end
    end.

Lemma follow_word_nonempty: forall tree word,
  tree != Empty -> exists word', follow_word tree word = Some word'.
Proof.
  elim => [//|l Hl r Hr]; case => [/= _|].
  - case: (any_leaf l) => [word'|]; first by exists (true::word').
    case: (any_leaf r) => [word'|]; first by exists (false::word').
    by exists [::].
  - case => /= word _.
  -- case: r Hr => [_|rl rr Hr]; first by exists [::].
     move: (Hr word) => [//|word' ->]; by exists (true::word').
  -- case: l Hl => [_|ll lr Hl]; first by exists [::].
     move: (Hl word) => [//|word' ->]; by exists (false::word').
Qed.

Lemma follow_word_comparable: forall tree word word',
  follow_word tree word = Some word' -> word' >=< word.
Proof.
  move => tree word word'.
  elim: tree word word' => [//|l Hl r Hr]; case => [word' _ |];
    first by rewrite seqprefix_comparables0.
  case => word word' /=;
  case H: (follow_word _ _) => [word''|] [] <- //;
  rewrite seqprefix_comparable_cons /=.
  - by apply Hr.
  - by apply Hl.
Qed.

Lemma follow_word_in_tree: forall tree word word',
  follow_word tree word = Some word' -> word' \in code_of_tree tree.
Proof.
  elim => [//|l Hl r Hr].
  case => [/=|].
Admitted.

Fixpoint complete_tree (tree: binary_tree): bool :=
  match tree with
  | Empty => false
  | Node l r =>
    ((l == Empty) && (r == Empty)) ||
    (complete_tree l && complete_tree r)
  end.

Definition is_complete (P: seq binary_word): Prop :=
  (prefix_code P) /\
  (forall (u: binary_word), exists (v: binary_word),
   (v \in P) && (u >=< v)).

Definition complete (P: seq binary_word): bool :=
  (prefix_code P) && (complete_tree (tree_of_code P)).

Lemma completeP: forall P,
  reflect (is_complete P) (complete P).
Proof.
  move => P; apply (iffP andP).
  - case => HP Htree; split => [//|u].
    pose v := (follow_word (tree_of_code P) u).
Admitted.

