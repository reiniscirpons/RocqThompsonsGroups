Require Import ssreflect ssrbool ssrfun.
From HB Require Import structures.
From mathcomp Require Import ssrnat eqtype choice div seq preorder.
From Thompson Require Import PrefixOrder.

Import Order.PreorderTheory.

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

(* TODO(reiniscirpons): Maybe do sets? *)
Definition binary_code := seq binary_word.

(* TODO(reiniscirpons): Explicitly mention prefix codes are finite
   in this development *)
Fixpoint prefix_code (code: binary_code): bool :=
  match code with
  | nil => true
  | word::code' =>
    (all (fun word' => word' >< word) code') &&
    (prefix_code code')
  end.

(* The following lemma establishes that the `prefix_code` function
    coincides with the mathematical definition of a prefix code. *)
Lemma prefix_codeP: forall code,
  reflect
    (uniq code /\
      (forall word1 word2,
        word1 \in code ->
        word2 \in code ->
        word1 >=< word2 ->
        word1 = word2))
    (prefix_code code).
Proof.
  move => code; apply (iffP idP) => /= [|[]].
  - elim: code => /= [//|word code IH /andP [/allP Hcomp /IH {IH} [-> H]]].
    split => [|word1 word2].
  -- apply /andP; split => [|//].
     apply /memPn => /= word' /Hcomp.
     apply contra => /eqP ->.
     Locate comparablexx.
     by exact: comparablexx.
  -- rewrite !in_cons => /orP [/eqP ->|H1] /orP [/eqP ->|H2] //.
  --- by rewrite comparable_sym; move: H2 => /Hcomp /negP.
  --- by move: H1 => /Hcomp /negP.
  --- by move => H3; apply H.
  - elim: code => /= [//|word code IH /andP [/memPn Hword Huniq] H].
    apply /andP; split.
  -- apply /allP => word' Hword'.
     apply /negP => Hcomp.
     enough (Heq: word = word').
  --- move: (Hword word' Hword') => /eqP; by rewrite Heq.
  --- apply H.
  ---- by rewrite in_cons eq_refl.
  ---- by rewrite in_cons Hword'; apply /orP; right.
  ---- by rewrite comparable_sym.
  -- apply IH => [//|word1 word2 H1 H2 Hcomp].
     apply H => [||//]; rewrite in_cons; apply /orP; by right.
Qed.

Definition prepend (letter: bool) (code: binary_code): binary_code :=
  [seq letter::word | word <- code].

Lemma prefix_code_prepend: forall letter code,
  prefix_code code -> prefix_code (prepend letter code).
Proof.
  move => letter; elim => [//|word code'] /= IH /andP [/allP H /IH H'].
  apply /andP; split => [|//].
  apply /allP => word' /mapP /= [word'' /H H'' ->].
  by rewrite seqprefix_comparable_cons eq_refl /=.
Qed.

Lemma prepend_uniq: forall (letter: bool) (code: binary_code),
  uniq code -> uniq (prepend letter code).
Proof.
  move => letter; elim => [//|word code IH /= /andP [Hw /IH ->]].
  apply /andP; split => [|//].
  apply /memPn => word' /mapP [word'' Hw'' ->].
  apply /eqP; case => H; rewrite H in Hw''.
  by move/negP: Hw.
Qed.

Lemma prefix_code_behead: forall word code,
  prefix_code (word::code) -> prefix_code code.
Proof.
  by move => word code /= /andP [].
Qed.

Lemma prefix_code_cons_nil: forall code,
  prefix_code ([::]::code) -> code = [::].
Proof.
  by case => [//|]; case.
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

Fixpoint tree_of_code (code: binary_code): binary_tree :=
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

Fixpoint code_of_tree (tree: binary_tree): binary_code :=
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

Lemma binary_code_of_binary_tree_prefix_code: forall tree,
  prefix_code (code_of_tree tree).
Proof.
  elim => [//|l /prefix_codeP /= [Hlu Hlc] r /prefix_codeP /= [Hru Hrc]].
  case: ifP => [//|_].
  apply /prefix_codeP; split => [|word1 word2].
  - rewrite cat_uniq !prepend_uniq /= => [|//|//].
    apply /andP; split => [|//].
    by apply /negP => /hasP [word /mapP [wordl _ ->] /mapP [wordr _ []]].
  - rewrite !mem_cat => /orP [|] /mapP [word1' H1 -> {word1}] 
                        /orP [|] /mapP [word2' H2 -> {word2}] //;
    rewrite seqprefix_comparable_cons => H;
    apply f_equal.
  -- by apply Hlc.
  -- by apply Hrc.
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

(* TODO(reiniscirpons): For this lemma, we need to assume that
   code is sorted, otherwise we cannot prove it. *)
(*Lemma code_of_treeK: forall code,*)
(*  prefix_code code ->*)
(*  code_of_tree (tree_of_code code) = code.*)
(*Proof.*)
(*  elim => [//|[|letter word] code IH];*)
(*    first by move/prefix_code_cons_nil => ->.*)
(*  move => /= /andP [];*)
(*  case: letter => Hword /= /IH;*)
(*  case: (tree_of_code code) => [<- /=|l r].*)
(*  1,3: rewrite code_of_tree_linear_tree /=;*)
(*       move: (linear_tree_non_empty word);*)
(*       by case: (linear_tree word) => [//|l r _].*)
(*  - move => /=.*)
(*Admitted.*)

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
Qed.

Fixpoint complete_tree (tree: binary_tree): bool :=
  match tree with
  | Empty => false
  | Node l r =>
    ((l == Empty) && (r == Empty)) ||
    (complete_tree l && complete_tree r)
  end.

Definition is_complete (P: binary_code): Prop :=
  (prefix_code P) /\
  (forall (u: binary_word), exists (v: binary_word),
   (v \in P) && (u >=< v)).

Definition complete (P: binary_code): bool :=
  (prefix_code P) && (complete_tree (tree_of_code P)).

Lemma completeP: forall P,
  reflect (is_complete P) (complete P).
Proof.
  move => P; apply (iffP andP).
  - case => HP Htree; split => [//|u].
    pose v := (follow_word (tree_of_code P) u).
Admitted.



