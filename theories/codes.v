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
   x >=< y <-> x and y are comparable
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

(* TODO(reiniscirpons): Add a notion of completeness. *)
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


Definition Leaf := Node Empty Empty.
Definition Caret := Node Leaf Leaf.

Fixpoint add_word (tree: binary_tree) (word: binary_word): binary_tree :=
  match word with
  | nil => tree
  | false::word' =>
    match tree with
    | Empty => Node (add_word Empty word') Empty
    | Node l r => Node (add_word l word') r
    end
  | true::word' =>
    match tree with
    | Empty => Node Empty (add_word Empty word')
    | Node l r => Node l (add_word r word')
    end
  end.

Fixpoint any_leaf (tree:binary_tree): option binary_word :=
  match tree with
  | Empty => None
  | Node l r =>
    match any_leaf l with
    | None => match any_leaf r with
      | None => None
      | Some w => Some (true::w)
      end
    | Some w => Some (false::w)
    end
  end.

Fixpoint follow_word (tree: binary_tree) (word: binary_word):
  option binary_word :=
    match tree, word with
    | Empty, _ => None
    | _, nil => any_leaf tree
    | Node l r, false::word' =>
      match follow_word l word' with
      | None => None
      | Some lw' => Some (false::lw')
      end
    | Node l r, true::word' =>
      match follow_word r word' with
      | None => None
      | Some rw' => Some (false::rw')
      end
    end.

Fixpoint tree_of_code (code: binary_code): binary_tree :=
  match code with
  | nil => Empty
  | word::code' => add_word (tree_of_code code') word
  end.

Fixpoint code_of_tree (tree: binary_tree): binary_code :=
  match tree with
  | Empty => nil
  | Node l r =>
    (prepend false (code_of_tree l)) ++
    (prepend true (code_of_tree r))
  end.

Lemma binary_code_of_binary_tree_prefix_code: forall tree,
  prefix_code (code_of_tree tree).
Proof.
  elim => [//|l /prefix_codeP /= [Hlu Hlc] r /prefix_codeP /= [Hru Hrc]].
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

Lemma code_of_treeK: forall code,
  prefix_code code ->
  code_of_tree (tree_of_code code) = code.
Proof.
  elim => [//|word code IH /= /andP [H /IH {}IH]].
  case: word H => /= [|].
Admitted.

Lemma tree_of_codeK: forall tree,
  tree_of_code (code_of_tree tree) = tree.
Proof.
  elim => [//|l Hl r Hr] /=.
Admitted.

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



