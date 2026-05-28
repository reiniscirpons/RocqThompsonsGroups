Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype div seq.

(*
  Initially:
    Binary 1-rooted 
    F, T, V groups
  Milestone:
    F is finitely generated
*)
Definition binary_word := seq bool.

Definition comparable (word1 word2: binary_word): bool :=
  (prefix word1 word2) || (prefix word2 word1).

Lemma comparable_refl: forall word, comparable word word.
Proof.
  by move => word; rewrite /comparable prefix_refl.
Qed.

Lemma comparable_symm: forall word1 word2,
  comparable word1 word2 -> comparable word2 word1.
Proof.
  by move => word1 word2; rewrite /comparable orbC.
Qed.

Lemma comparable_cons: forall letter word1 word2,
  comparable (letter::word1) (letter::word2) =
  comparable word1 word2.
Proof.
  by move => letter word1 word2; rewrite /comparable !prefix_cons !eq_refl.
Qed.

(* TODO(reiniscirpons): Maybe do sets? *)
Definition binary_code := seq binary_word.

Fixpoint prefix_code (code: binary_code): bool :=
  match code with
  | nil => true
  | word::code' =>
    (all (fun word' => ~~ (comparable word' word)) code') &&
    (prefix_code code')
  end.

(*| The following lemma establishes that the `prefix_code` function
    coincides with the mathematical definition of a prefix code. |*)
Lemma prefix_codeP: forall code,
  reflect
    (uniq code /\
      (forall word1 word2,
        word1 \in code ->
        word2 \in code ->
        comparable word1 word2 ->
        word1 = word2))
    (prefix_code code).
Proof.
  move => code; apply (iffP idP) => /= [|[]].
  - elim: code => /= [//|word code IH /andP [/allP Hcomp /IH {IH} [-> H]]].
    split => [|word1 word2].
  -- apply /andP; split => [|//].
     apply /memPn => /= word' /Hcomp.
     apply contra => /eqP ->.
     by exact: comparable_refl.
  -- rewrite !in_cons => /orP [/eqP ->|H1] /orP [/eqP ->|H2] //.
  --- by move/comparable_symm; move: H2 => /Hcomp /negP.
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
  ---- by rewrite comparable_symm.
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
  by rewrite comparable_cons.
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
    rewrite comparable_cons => H;
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




