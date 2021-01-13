(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrbool Bool List.

Set Implicit Arguments.

Axiom todo : forall {A}, A.
Ltac todo := by apply: todo.

(* ==================================================================== *)
(* This template contains incomplete definitions that you have to       *)
(* fill. We always used the keyword `Definition` for all of them but    *)
(* you are free to change for a `Fixpoint` or an `Inductive`.           *)
(*                                                                      *)
(* If needed, it is perfectly fine to add intermediate definitions and  *)
(* local lemmas.                                                        *)

(* ==================================================================== *)
(* In this project, we are going to develop and prove correct an        *)
(* algorithm for deciding the membership of a word w.r.t. a given       *)
(* regular language - all these terms are going to be defined below     *)

(* This project lies in the domain of *formal languages*. The study     *)
(* of formal languages is a branch of theoretical computer science and  *)
(* is about that is interested in the purely syntactical aspects of     *)
(* of languages and as applications in different domains, ranging from  *)
(* the definition of  the grammar of programming languages to the field *)
(* of automated translation.                                            *)

(* As with natural languages, we first need to fix an alphabet. In our  *)
(* case, we are simply going to declare a type `A : Type` - i.e. we     *)
(* will use the same alphabet for all the formal languages we are going *)
(* to study. Inhabitants of `A` are called `letters`.                   *)

Parameter (A : Type).

(* -------------------------------------------------------------------- *)
(* A `word` is then simply a finite sequence of letters of `A`. We      *)
(* denote by A* the set of words over `A`. In Coq, we are going to      *)
(* represent words as lists whose elements are inhabitants of `A`. This *)
(* naturally leads to the following definition:                         *)

Notation word := (list A).

(* -------------------------------------------------------------------- *)
(* You can get an overview of the List library at the following URL:    *)
(* https://coq.inria.fr/distrib/current/stdlib/Coq.Lists.List.html      *)

(* -------------------------------------------------------------------- *)
(* In this setting, a `language` is simply a subset of A*. Assuming     *)
(* that `x` & `y` are letters of A, we can define the following         *)
(* languages:                                                           *)
(*                                                                      *)
(*  - the empty language: `L = ∅`;                                      *)
(*                                                                      *)
(*  - the language that contains only the empty word ε (i.e. the only   *)
(*    (word of length 0): L = {ε}`;                                     *)
(*                                                                      *)
(*  - the language that contains all the words solely composed of the   *)
(*    letter `x`: L = { ε, x, xx, xxx, ... } = { xⁿ | n ∈ ℕ } (here,    *)
(*    xⁿ stands for the word x…x, where x is repeated n times);         *)
(*                                                                      *)
(*  - the language that contains all the words of the form xⁿyⁿ:        *)
(*    L = { xⁿyⁿ | n ∈ ℕ };                                             *)
(*                                                                      *)
(*  - if we assume that A contains the letter '[' & ']', we can         *)
(*    define the language of well-balanced words for '[' & ']':         *)
(*    L = { w ∈ { [, ] }* | s.t. P(w) && Q(w) }, where                  *)
(*      - P(w) = any prefix of w contain no more ]'s then ['s           *)
(*      - Q(w) = the number of ['s and ]'s of w are equal.              *)

(* --------------------------------------------------------------------      *)
(* We can also combine languages to form other languages. For example,       *)
(* if L and G are languages, we can define:                                  *)
(*                                                                           *)
(*  - the union of L & G            L ∪ G                                    *)
(*  - the concatenation of L & G    { w1 · w2 | w1 ∈ L, w2 ∈ G }             *)
(*  - the intersection of L & G     L ∩ G                                    *)
(*  - the complement of L           A* \ L                                   *)
(*  - the Kleene closure of L       L* = { w_1 ... w_n | n \in ℕ, w_i ∈ L }  *)
(*  - the mirror of L               rev(L) = { rev(w) | w ∈ L }              *)

(* -------------------------------------------------------------------- *)
(* To define languages in Coq, we need a way to represent subsets       *)
(* of A*, i.e. subsets of the set of `word`'s. To that end, we are      *)
(* going to represent a set using its indicator function. (We remind    *)
(* that, given a subset F of an ambient set E, the indicator function   *)
(* of F is the function f_E from E to { ⊤, ⊥ } s.t.                     *)
(*                                                                      *)
(*                     f_E(x) = ⊤ iff x ∈ E                             *)

(* In Coq, the codomain of its indicator function is going to be a      *)
(* proposition: given a function `F : E -> Prop`, we say that x belongs *)
(* to `x` iff `f x` holds.                                              *)

Notation language := (word -> Prop).

(* -------------------------------------------------------------------- *)
(* From now use, we assume that L, G, H denote languages, x, y denote   *)
(* letters and that and w denotes a word.                               *)

Implicit Types (L G H : language) (x y : A) (w : word).

(* -------------------------------------------------------------------- *)
(* From there, we can define the following languages                    *)

(* The empty language: no words belong to it.                           *)
(* (its indicator function always return `False`)                       *)
Definition lang0 : language :=
  fun w => False.

(* The language that only contains the empty word.                      *)
Definition lang1 : language :=
  fun w => w = nil.

(* Q1. We now ask you to define the following languages                 *)

(*  Given a word `w0`, the language that only contains the word `w0`.   *)
(* Q1. We now ask you to define the following languages                 *)

(*  Given a word `w0`, the language that only contains the word `w0`.   *)
Definition langW w0 : language := 
  fun w => w = w0.

(* Given a sequence `ws` of words, the language that contains all the   *)
(* the words `ws` and only these words.                                 *)
Definition langF (ws : list word) : language := 
  fun w => In w ws.

(* Given a letter `x`, the language that only contains the letter `x`   *)
(* seen as a word of length 1.                                          *)
Definition langA x : language := 
  fun w => w = cons x nil.

(* The union of the two languages `L` and `G`.                          *)
Definition langU L G : language := 
  fun w => (L w) \/ (G w).

(* The intersection of the two languages `L` and `G`.                   *)
Definition langI L G : language :=
  fun w => (L w) /\ (G w).

(* The concatenation of the two languages `L` and `G`.                  *)
Definition langS L G : language := 
  fun w => exists w1 w2, (w = app w1 w2) /\ (L w1) /\ (G w2).

(* The Kleene closure of the language `L`                               *)
Fixpoint langKn (L: language) (n: nat) : language := 
  match n with
  | 0 => lang1
  | S m => langS L (langKn L m)
  end.

Definition langK L : language :=
  fun w => exists n, langKn L n w.

(* The mirror of the language `L` (You can use the `rev`, that reversed *)
(* a list, from the standard library. *)
Definition langM L : language :=
  fun w => L (rev w).


(* -------------------------------------------------------------------- *)
(* Given two languages, we will consider `L` & `G` equal iff they       *)
(* contain the same words:                                              *)

Definition eqL L G := forall w, L w <-> G w.

Infix "=L" := eqL (at level 90).

(* Q2. Prove the following equivalances:                                *)

Lemma concat0L L : langS lang0 L =L lang0.
Proof.
move => w.
split.
move => p.
move: p => [w1 [w2 [p [q r]]]].
done.
done.
Qed.

Lemma concatL0 L : langS L lang0 =L lang0.
Proof.
move => w.
split.
move => p.
move: p => [w1 [w2 [p [q r]]]].
done.
done.
Qed.

Lemma concat1L L : langS lang1 L =L L.
Proof.
move => w.
split.
move => p.
move: p => [w1 [w2 [p [q r]]]].
have e: (w1 = nil).
done.
rewrite e in p.
have f: (w2 = nil ++ w2).
done.
rewrite -f in p.
rewrite p.
done.
move => p.
exists nil.
exists w.
done.
Qed.

Lemma concatL1 L : langS L lang1 =L L.
Proof.
move => w.
split.
move => [w1 [w2 [p [q r]]]].
have e: w2 = nil.
done.
rewrite e in p.
have f: (w1 = w1 ++ nil).
symmetry.
apply app_nil_r.
rewrite p.
rewrite -f.
done.
move => p.
exists w.
exists nil.
have e: w ++ nil = w.
apply app_nil_r.
rewrite e.
done.
Qed.

Lemma concatA L G H : langS (langS L G) H =L langS L (langS G H).
Proof.
move => w.
split.

move => [wLG [wH [eLGH [pLG pH]]]].
move: pLG => [wL [wG [eLG [pL pG]]]].
rewrite eLG in eLGH.
have e : w = wL ++ wG ++ wH.
rewrite eLGH.
symmetry.
apply app_assoc.
exists wL.
exists (wG ++ wH).
have f : langS G H (wG ++ wH).
exists wG.
exists wH.
done.
done.

move => [wL [wGH [eLGH [pL pGH]]]].
move: pGH => [wG [wH [eGH [pG pH]]]].
rewrite eGH in eLGH.
have e : w = (wL ++ wG) ++ wH.
rewrite eLGH.
apply app_assoc.
exists (wL ++ wG).
exists wH.
rewrite -e.
have f : langS L G (wL ++ wG).
exists wL.
exists wG.
done.
done.
Qed.

Lemma unionC L G : langU L G =L langU G L.
Proof.
move => w.
split.

move => [Lw | Gw].
right. done.
left. done.

move => [Gw | Lw].
right. done.
left. done.
Qed.

Lemma interC L G : langI L G =L langI G L.
Proof. 
move => w.
split.

move => [Lw Gw].
done.

move => [Gw Lw].
done.
Qed.

(* Additional lemmas to prove langKK *)
Lemma eqL_concat_l L G W: L =L G -> langS W L =L langS W G.
Proof.
move => p w.
split.
move => [i [j [e [f h]]]].
rewrite e.
exists i. 
exists j.
rewrite -p.
done.
move => [i [j [e [f h]]]].
rewrite e.
exists i. 
exists j.
rewrite p.
done.
Qed.

Lemma eqL_concat_r L G W: L =L G -> langS L W =L langS G W.
Proof.
move => p w.
split.
move => [i [j [e [f h]]]].
rewrite e.
exists i. 
exists j.
rewrite -p.
done.
move => [i [j [e [f h]]]].
rewrite e.
exists i. 
exists j.
rewrite p.
done.
Qed.

Lemma langKn_app : forall n m L, langS (langKn L n) (langKn L m) =L langKn L (n + m).
Proof.
induction n.
simpl.
move => L w.
apply concat1L.
simpl.
move => m L w.
have e : langS (langS L (langKn L n)) (langKn L m)  w <-> langS L (langS (langKn L n) (langKn L m)) w.
apply concatA.
apply iff_trans with (langS L (langS (langKn L n) (langKn L m)) w).
apply e.
apply eqL_concat_l.
apply IHn. 
Qed.

Lemma langKn_K : forall n L w, langKn (langK L) n w -> langK L w.
Proof.
induction n.
simpl.
exists 0.
done.
simpl.
move => L w.
move => [w1 [w2 [e [f g]]]].
move: f => [m f].
have h: langK L w2.
apply IHn.
done.
move: h => [k h].
exists (m + k).
apply langKn_app.
exists w1.
exists w2.
split.
done.
split.
done.
done.
Qed.

Lemma langKK L : langK (langK L) =L langK L.
Proof.
split.
+ move => [n e].
induction n.
simpl in e.
exists 0.
done.
simpl in e.
move: e => [w1 [w2 [e [[m f] g]]]].
have p: langK L w2.
apply (langKn_K n).
done.
have ex_k: exists k, langKn L k w2.
done.
move: ex_k => [k h].
exists (m + k).
apply langKn_app.
exists w1.
exists w2.
split.
done.
split.
done.
done.
+ move => e.
exists 1.
simpl.
apply concatL1.
done.
Qed.

(* Note that, since languages are represented as indicator functions    *)
(* over `Prop`, we cannot assess that `L =L G` implies `L = G`.         *)

(* ==================================================================== *)
(*                          REGULAR LANGUAGES                           *)

(* We are now interested in a subclass of languages called "regular     *)
(* languages": a language `L` is said to be regular iff one of the      *)
(* following holds:                                                     *)
(*                                                                      *)
(*  - L = ∅ or L = {ε} or L = {x} for some x ∈ A ;                      *)
(*  - L = L1 ∪ L2 for L1, L2 regular languages ;                        *)
(*  - L = L1 · L2 for L1, L2 regular languages ;                        *)
(*  - L = G* for G a regular language.                                  *)

(* This kind of inductive definitions can be encoded in Coq using       *)
(* an inductive predicate `regular : language -> Prop` s.t.             *)
(*                                                                      *)
(*             L is regular iff `regular L` holds                       *)

(* Q3. complete the following definition of the predicate `regular`:    *)

Inductive regular : language -> Prop :=
  (* Any language equivalent to a regular language is regular *)
| REq L G of regular L & G =L L : regular G

  (* The empty language is regular *)
| REmpty : regular lang0
| REmp_word : regular lang1
| RLetter x: regular (langA x)
| RUnion L G of regular L & regular G: regular (langU L G)
| RConcatenation L G of regular L & regular G: regular(langS L G)
| RKleene L of regular L: regular (langK L).

Lemma eqL_word_concat a w : langW (a::w) =L (langS (langA a) (langW w)).
Proof.
move => g.
split; case g; try done.
move => a0 l p.
move: p => [i j].
rewrite i. rewrite j.
exists (cons a nil).
exists w. 
done.
move => k.
move: k => [i [j [h [k l]]]].
rewrite h. 
have m: i = cons a nil.
apply k.
have n: j = w.
apply l.
rewrite m. rewrite n.
done.
move => a0 l p.
move: p => [i [j [h [k p]]]].
rewrite h.
rewrite k.
rewrite p.
done.
Qed.

Lemma eqL_commutative L G: L =L G -> G =L L.
Proof.
move => p.
move => w.
split.
apply p.
apply p.
Qed.

Lemma eqL_transitive L G W: L =L G -> G =L W -> W =L L.
Proof.
move => p q w.
split.
move => h.
apply p.
apply q.
apply h.
move => h.
apply q.
apply p.
apply h.
Qed.

Lemma langKn_langS L n: langS L (langKn L n) =L langS (langKn L n) L.
Proof.
induction n.
simpl.
split.
rewrite concat1L.
rewrite concatL1.
done.
rewrite concat1L.
rewrite concatL1.
done.
simpl.


have j: langS (langS L (langKn L n)) L =L langS L (langS (langKn L n) L).
apply concatA.
have e: langS L (langS (langKn L n) L) =L langS L (langS L (langKn L n)).
apply eqL_commutative.
apply eqL_concat_l.
done.
have final: langS (langS L (langKn L n)) L =L langS L (langS (langKn L n) L) ->
langS L (langS (langKn L n) L) =L langS L (langS L (langKn L n)) -> 
langS L (langS L (langKn L n)) =L langS (langS L (langKn L n)) L.
apply eqL_transitive.
auto.
Qed.

Lemma langM_langS L G: langS (langM L) (langM G) =L langM (langS G L).
Proof.
split.
move => [i [j [e [f h]]]].
rewrite e.
have final: (langS G L) (rev (i ++ j)).
exists (rev j).
exists (rev i).
have f1: L (rev i).
done.
have h1: G (rev j).
done.
have k: rev (i++j) = rev j ++ rev i.
apply rev_eq_app.
apply rev_involutive.
done.
done.
move => [i [j [e [f h]]]].
exists (rev j).
exists (rev i).
have a: w = rev j ++ rev i.
apply rev_eq_app.
done.
have f1: G (rev (rev i)).
rewrite rev_involutive.
done.
have h1: L (rev (rev j)).
rewrite rev_involutive.
done.
done.
Qed.


Lemma langKn_langM L n: langKn (langM L) n =L langM (langKn L n).
Proof.
induction n.
split.
move => p.
simpl.
simpl in p.
have e: w = nil.
done.
rewrite e.
done.
simpl.
move => p.
simpl in p.
have h: w = rev nil.
have e: rev w = nil.
done.
have s: rev (rev w) = rev nil.
rewrite e.
done.
rewrite rev_involutive in s.
done.
done.
simpl.
have i: langS (langKn (langM L) n)(langM L) =L langS (langM (langKn L n))(langM L).
apply eqL_concat_r.
done.
have j: langS (langM (langKn L n))(langM L) =L langM (langS L (langKn L n)).
apply langM_langS.
have k:langM (langS L (langKn L n)) =L langS (langKn (langM L) n) (langM L).
have f: langS (langKn (langM L) n) (langM L) =L langS (langM (langKn L n)) (langM L) ->
langS (langM (langKn L n)) (langM L) =L langM (langS L (langKn L n)) ->
langM (langS L (langKn L n)) =L langS (langKn (langM L) n) (langM L).
apply eqL_transitive.
auto.
have h: langS (langKn (langM L) n) (langM L) =L langS (langM L)(langKn (langM L) n).
apply eqL_commutative.
apply langKn_langS.
have final: langM (langS L (langKn L n)) =L langS (langKn (langM L) n) (langM L) ->
langS (langKn (langM L) n) (langM L) =L langS (langM L) (langKn (langM L) n) ->
langS (langM L) (langKn (langM L) n) =L langM (langS L (langKn L n)).
apply eqL_transitive.
auto.
Qed.

(* -------------------------------------------------------------------- *)
(* Q4. prove that `langW w` is regular.                                 *)
Lemma regularW w : regular (langW w).
Proof.
induction w.
apply REmp_word.
have e: regular (langA a).
apply RLetter.
have f: regular (langS (langA a) (langW w)).
apply RConcatenation; auto.
have j: langW (a::w) =L langS (langA a) (langW w).
apply eqL_word_concat.
apply REq with (langS (langA a) (langW w)).
done.
done.
Qed.

(* -------------------------------------------------------------------- *)
(* Q5. prove that `langM L` is regular, given that L is regular.        *)
Lemma regularM L : regular L -> regular (langM L).
Proof. 
move => p.
induction p.
have k: langM G =L langM L.
move => w.
split.
move => i.
have e:  G (rev w).
done.
have j: L (rev w).
apply H.
done.
done.
move => i.
have e:  L (rev w).
done.
have j: G (rev w).
apply H.
done.
done.
apply REq with (langM L).
done.
done.

apply REmpty.

have j: langM lang1 =L lang1.
split.
move => p.
have e: lang1 (rev w).
done.
have k: rev w = nil.
done.
have s: rev (rev w) = w.
apply rev_involutive.
have f: w = rev nil.
rewrite -k. 
rewrite s.
done.
have final: w = nil.
done.
rewrite final.
done.
move => p.
have k: w = nil.
done.
rewrite k.
done.
apply REq with (lang1).
apply REmp_word.
done.

have j: langM (langA x) =L langA x.
split.
move => p.
have e: rev w = (cons x nil).
done.
have k: rev (rev w) = rev(cons x nil).
rewrite e.
done.
have j: rev(rev (w)) = w.
apply rev_involutive.
rewrite j in k.
done.
move => p.
have e: w = (cons x nil).
done.
have j: rev (x :: nil) = x :: nil.
done.
rewrite -j in e.
have i: rev w = (x :: nil).
have k: rev(rev (x :: nil)) = x :: nil.
apply rev_involutive.
have h: rev w = rev (rev (x :: nil)).
rewrite e.
done.
rewrite -h in k.
done.
done.
apply REq with (langA x).
apply RLetter.
done.

have j: langM (langU L G) =L langU (langM L) (langM G).
done.
have i: regular (langU (langM L) (langM G)).
apply RUnion; auto.
apply REq with (langU (langM L) (langM G)).
done.
done.

have j: langM (langS L G) =L langS (langM G) (langM L).
split.
move => p.
move: p => [i [h [k [l p]]]].
have e: w = rev h ++ rev i.
apply rev_eq_app.
done.
exists (rev h).
exists (rev i).
split.
done.
split.
have a: rev(rev h) = h.
apply rev_involutive.
have b: G (rev(rev h)).
rewrite a.
done.
done.
have a: rev(rev i) = i.
apply rev_involutive.
have b: L (rev(rev i)).
rewrite a.
done.
done.
move => p.
move: p => [i [h [k [l p]]]].
have e: (langS L G) (rev w).
have j: rev w = (rev h) ++ (rev i).
apply rev_eq_app.
rewrite k.
apply rev_involutive.
rewrite j.
exists (rev h).
exists (rev i).
done.
done.
apply REq with (langS (langM G) (langM L)).
apply RConcatenation.
done.
done.
done.




have e: (langK (langM L)) =L (langM (langK L)).
split.
move => [n i].
induction n.
simpl in i.
have k: w = nil.
done.
have f: rev nil = nil.
done.
rewrite k.
have e: (langK L) (rev nil).
rewrite f.
exists 0.
simpl.
done.
done.
simpl in i.
move: i => [a [b [h [j k]]]].
have f: (langK L) (rev w).
have m: rev w = rev b ++ rev a.
apply rev_eq_app.
rewrite rev_involutive.
done.
rewrite m.
exists (S n).
simpl.
apply langKn_langS.
exists (rev b).
exists (rev a).
have j1: L (rev a).
done.
have k1: langKn L n (rev b).
apply langKn_langM.
done.
done.
done.
move => [n i].
exists n.
apply langKn_langM.
done.
have final: regular (langK (langM L)).
apply RKleene.
done.
apply REq with (langK (langM L)).
done.
apply eqL_commutative.
done.
Qed.


(* ==================================================================== *)
(*                        REGULAR EXPRESSIONS                           *)

(* Related to regular languages is the notion of regular expressions.   *)
(* A regular expression is a formal, syntactic expression that can      *)
(* latter be interpreted as a regular language. Regular expressions are *)
(* pervasive in computer science, e.g. for searching for some text in   *)
(* a file, as it is possible with the `grep` command line tool.         *)
(*                                                                      *)
(* For instance, the command:                                           *)
(*                                                                      *)
(*    grep -E 'ab*a' foo.txt                                            *)
(*                                                                      *)
(* is going to print all the lines of `foo.txt` that contains a word    *)
(* of the form ab⋯ba (where the letter b can be repeated 0, 1 or more   *)
(* time. I.e., grep is going to find all the lines of `foo.txt` that    *)
(* contains a word that belongs in the formal language:                 *)
(*                                                                      *)
(*    L = { abⁿa | n ∈ ℕ }                                              *)
(*                                                                      *)
(* If you need to convince yourself that L is regular, note that:       *)
(*                                                                      *)
(*    L = { a } ∪ { b }* ∪ { a }                                        *)
(*                                                                      *)
(* In some sense, a regular expression is just a compact way to         *)
(* represent a regular language, and its definition is going to be      *)
(* close to the one of regular languages.                               *)
(*                                                                      *)
(* A regular expression is either:                                      *)
(*                                                                      *)
(*  - the constant ∅ or the constant ε or one letter from A             *)
(*  - the disjunction r1 | r2 of two regular expressions                *)
(*  - the concatenation r1 · r2 of two regular expressions              *)
(*  - the Kleene r* of some regular expression                          *)

(* We can represent regular expressions as a inductive type in Coq.     *)

(* Q6. complete the following definition:                               *)

Inductive regexp : Type :=
| RE_Empty : regexp
| RE_Void  : regexp
| RE_Atom  : A -> regexp

  (* TO BE COMPLETED *)
| RE_Union : regexp -> regexp -> regexp
| RE_Concat : regexp -> regexp -> regexp
| RE_Kleene : regexp -> regexp.

Implicit Types (r : regexp).

(* We now have to formally related regular expressions to regular       *)
(* languages. For that purpose, we are going to interpret a regular     *)
(* expression as a languages. If r is a regular expression, then we     *)
(* denote by language [r] as follows:                                   *)
(*                                                                      *)
(*   - [∅]       = ∅                                                    *)
(*   - [ε]       = ε                                                    *)
(*   - [a]       = { a } for a ∈ A                                      *)
(*   - [r₁ ∪ r₂] = [r₁] ∪ [r₂]                                          *)
(*   - [r₁ · r₂] = [r₁] · [r₂]                                          *)
(*   - [r*]      = [r]*                                                 *)

(* Q7. implement the Coq counterpart of the above definition:           *)

Fixpoint interp (r : regexp) {struct r} : language :=
  match r with
  | RE_Empty => lang0
  | RE_Void => lang1
  | RE_Atom a => langA a
  | RE_Union r1 r2 => langU (interp r1) (interp r2)
  | RE_Concat r1 r2 => langS (interp r1) (interp r2)
  | RE_Kleene r1 => langK (interp r1)
  end.

(* Q8. show that the interpretation of a regular expression is a        *)
(*     regular language:                                                *)

Lemma regular_regexp r : regular (interp r).
Proof.
induction r; simpl.
apply REmpty.
apply REmp_word.
apply RLetter.
apply RUnion; done.
apply RConcatenation; done.
apply RKleene. 
done.
Qed.

(* Additional lemmas to prove Q9 *)
Lemma eqL_langU L1 G1 L2 G2 : (L1 =L L2) /\ (G1 =L G2) -> langU L1 G1 =L langU L2 G2.
Proof.
move => [p q] w.
split.
move => [hl | hg].
left. apply p. done.
right. apply q. done.
move => [hl | hg].
left. apply p. done.
right. apply q. done.
Qed.

Lemma eqL_langS L1 G1 L2 G2 : (L1 =L L2) /\ (G1 =L G2) -> langS L1 G1 =L langS L2 G2.
Proof.
move => [p q] w.
split.
move => [w1 [w2 [hw [hl hg]]]].
exists w1. exists w2.
split.
done.
split.
apply p. done.
apply q. done.
move => [w1 [w2 [hw [hl hg]]]].
exists w1. exists w2.
split.
done.
split.
apply p. done.
apply q. done.
Qed.

Lemma eqL_langKn L1 L2 n: L1 =L L2 -> langKn L1 n =L langKn L2 n.
Proof.
move => p.
induction n.
done.
simpl.
apply eqL_langS.
split.
done.
done.
Qed.

Lemma eqL_langK L1 L2: L1 =L L2 -> langK L1 =L langK L2.
Proof.
move => p.
split.
move => [n h].
exists n.
apply eqL_langKn with L1.
apply eqL_commutative.
done.
done.
move => [n h].
exists n.
apply eqL_langKn with L2.
done.
done.
Qed.

(* Q9. show that any regular language can be interpreted as a           *)
(*     regular expression:                                              *)

Lemma regexp_regular L : regular L -> exists r, L =L interp r.
Proof.
move => p.
induction p.
+ move: IHp => [r f].
exists r.
apply eqL_transitive with L.
apply eqL_commutative.
done.
apply eqL_commutative.
done.
+ exists RE_Empty.
done.
+ exists RE_Void.
done.
+ exists (RE_Atom x).
done.
+ move: IHp1 => [r1 h1].
move: IHp2 => [r2 h2].
exists (RE_Union r1 r2).
simpl.
apply eqL_langU.
done.
+ move: IHp1 => [r1 h1].
move: IHp2 => [r2 h2].
exists (RE_Concat r1 r2).
simpl.
apply eqL_langS.
done.
+ move: IHp => [r h].
exists (RE_Kleene r).
simpl.
apply eqL_langK.
done.
Qed.

(* Of course, it may happen that two regular expressions represent      *)
(* the same language: r1 ~ r2 iff [r1] = [r2].                          *)

(* Q10. write a binary predicate eqR : regexp -> regexp -> Prop s.t.    *)
(*      eqR r1 r2 iff r1 and r2 are equivalent regexp.                  *)
Definition eqR (r1 r2 : regexp) : Prop := (interp r1) =L (interp r2).

Infix "~" := eqR (at level 90).

(* Additional lemmas for Q11 *)

Lemma langKn_imply L G n: (forall w, L w -> G w) -> (forall w, langKn L n w -> langKn G n w).
Proof.
induction n.
done.
simpl.
move => p w e.
move: e => [a [b [j [k i]]]].
rewrite j.
have k1: G a.
auto.
have i1: langKn G n b.
auto.
exists a.
exists b.
done.
Qed.


Lemma langK_imply L G: (forall w, L w -> G w) -> (forall w, langK L w -> langK G w).
Proof.
move => w p [n h].
exists n.
apply langKn_imply with L.
done.
done.
Qed.


(* Q11. state and prove the following regexp equivalence:               *)
(*           (a|b)* ~ ( a*b* )*                                         *)

Lemma union_kleene (r1 r2: regexp) : RE_Kleene(RE_Union r1 r2) ~ RE_Kleene(RE_Concat(RE_Kleene r1)(RE_Kleene r2)).
Proof.
move => w.
simpl.
split.
move => h.
have f: forall w, langU (interp r1) (interp r2) w -> langS (langK (interp r1)) (langK (interp r2)) w.
move => w0 p.
move: p => [a | b].
exists w0.
exists nil.
split.
rewrite app_nil_r.
done.
split.
exists (S 0).
simpl.
apply concatL1.
done.
exists 0.
done.
exists nil.
exists w0.
split.
done.
split.
exists 0.
simpl.
done.
exists (S 0).
simpl.
apply concatL1.
done.

apply langK_imply with (langU (interp r1) (interp r2) ).
done.
done.
have f: forall w0, langS (langK (interp r1)) (langK (interp r2)) w0 -> langK (langU (interp r1) (interp r2)) w0.
move => w0.
move => [w1 [w2 [p [h g]]]].
move: h => [n h].
move: g => [m g].
exists (n + m).
apply langKn_app.
exists w1.
exists w2.
split.
done.
split.
apply langKn_imply with (interp r1).
move => w3 p3.
left. done.
done.
apply langKn_imply with (interp r2).
move => w3 p3.
right. done.
done.
have g: forall w0,
    langK (langS (langK (interp r1)) (langK (interp r2))) w0 -> langK (langK (langU (interp r1) (interp r2))) w0.
apply langK_imply.
done.
have h: langK (langK (langU (interp r1) (interp r2))) w -> langK (langU (interp r1) (interp r2)) w.
apply langKK.
move => q.
auto.
Qed.

(* ==================================================================== *)
(*                          REGEXP MATCHING                             *)

(* We now want to write a algorithm for deciding if a given word `w`    *)
(* matches a regular expression `r`, i.e. for deciding wether `w ∈ [r]` *)
(*                                                                      *)
(* For that purpose, we are going to use Brzozowski's derivatives.      *)
(*                                                                      *)
(* The idea of the algorithm is the following:                          *)
(*                                                                      *)
(* Given a letter `x` and an regular expression `r`, the Brzozowski's   *)
(* derivatives of `x` w.r.t. `r` is a regular expression x⁻¹·r s.t.     *)
(*                                                                      *)
(*    x · w ∈ [r] ⇔ w ∈ [x⁻¹·r]                                         *)
(*                                                                      *)
(* Assuming that we can compute a Brzozowski's derivative for any       *)
(* letter `x` and regular expression `r`, one can check that a word `w` *)
(* matches a regexp `r` as follows:                                     *)
(*                                                                      *)
(*   - if w = x · w' for some letter x and word w', we recursively      *)
(*     check that `w` matches `x⁻¹·r`; otherwise                        *)
(*   - if w = ε, then we directly check that [r] contains the empty     *)
(*     word - a property that is deciable.                              *)

(* Q12. write a nullity test `contains0` : regexp -> bool s.t.          *)
(*                                                                      *)
(*      ∀ r, contains0 r ⇔ ε ∈ [e]                                      *)

Fixpoint contains0 (r : regexp) : bool := 
  match r with
  | RE_Empty => false
  | RE_Void => true
  | RE_Atom a => false
  | RE_Union r1 r2 => (contains0 r1) || (contains0 r2)
  | RE_Concat r1 r2 => (contains0 r1) && (contains0 r2)
  | RE_Kleene r1 => true
  end.

(* Q13. prove that your definition of `contains0` is correct:           *)

Lemma contains0_ok r : contains0 r <-> interp r nil.
Proof.
split.
move => p.
induction r; try done.
simpl in p.
simpl.
move/orP: p => p.
move: p => [a | b].
left.
auto.
right.
auto.
simpl in p.
move/andP: p => p.
move: p => [a b].
simpl.
exists nil.
exists nil.
auto.
simpl.
exists 0.
done.

induction r; try done.
move => p.
simpl.
simpl in p.
move: p => [a | b].
apply/orP.
left.
auto.
apply/orP.
right.
auto.

simpl.
move => [w [k [h [j i]]]].
apply/andP.
have e: w = nil /\ k = nil.
apply app_eq_nil.
done.
move: e => [e1 e2].
rewrite e1 in j.
rewrite e2 in i.
split.
auto.
auto.
Qed.

(* We give below the definition of the Brzozowski's derivative:         *)
(*                                                                      *)
(*   - x⁻¹ · x         = ε                                              *)
(*   - x⁻¹ · y         = ∅ if x ≠ y                                     *)
(*   - x⁻¹ · ε         = ∅                                              *)
(*   - x⁻¹ · ∅         = ∅                                              *)
(*   - x⁻¹ · (r₁ | r₂) = (x⁻¹ · r₁) | (x⁻¹ · r₂)                        *)
(*   - x⁻¹ · (r₁ · r₂) = (x⁻¹ · r₁) · r₂ | E(r₁) · (x⁻¹ · r₂)           *)
(*   - x⁻¹ · r*        = (x⁻¹ · r) · r*                                 *)
(*                                                                      *)
(* where E(r) = ε if ε ∈ [r] & E(r) = ∅ otherwise.                      *)

(* Q14. write a function `Brzozowski` that computes a Brzozowski's      *)
(*      derivative as defined above.                                    *)
(*                                                                      *)
(* For that purpose, you may need to have a decidable equality over     *)
(* `A`. The parameter `Aeq` along with the axioms `Aeq_dec` give        *)
(* you such a decidable equality.                                       *)

Parameter Aeq : A -> A -> bool.

(* Here, `Aeq x y` has to be read as `Aeq x y = true`                   *)
Axiom Aeq_dec : forall (x y : A), Aeq x y <-> x = y.

Fixpoint Brzozowski (x : A) (r : regexp) : regexp :=
  match r with
  | RE_Empty => RE_Empty
  | RE_Void => RE_Empty
  | RE_Atom y => if Aeq x y then RE_Void else RE_Empty
  | RE_Union r1 r2 => RE_Union (Brzozowski x r1) (Brzozowski x r2)
  | RE_Concat r1 r2 => 
    if contains0 r1 then RE_Union (RE_Concat (Brzozowski x r1) r2) (Brzozowski x r2) 
    else RE_Concat (Brzozowski x r1) r2
  | RE_Kleene r1 => RE_Concat (Brzozowski x r1) (RE_Kleene r1)
  end.

(* Q15. write a function `rmatch` s.t. `rmatch r w` checks wether a     *)
(*      word `w` matches a given regular expression `r`.                *)

Fixpoint rmatch (r : regexp) (w : word) : bool := 
  match w with 
  | nil => contains0 r
  | x :: w1 => rmatch (Brzozowski x r) w1 
  end.

(* Q16. show that the `Brzozowski` function is correct.                 *)

Lemma Brzozowski_correct_aux (x : A) (r : regexp) :
  forall w, interp (Brzozowski x r) w -> interp r (x :: w).
Proof.
induction r; try done; move => w.
move => p.
simpl.
simpl in p.

+ case e: (Aeq x a).
rewrite e in p.
simpl in p.
rewrite p.
have i: x = a.
apply Aeq_dec.
done.
rewrite i.
done.
rewrite e in p.
simpl in p.
done.

+ move => p.
simpl in p.
move: p => [p1 | p2].
simpl.
left. auto.
right. auto.

+ move => p.
simpl in p.
simpl.
case e: (contains0 r1).
rewrite e in p.
simpl in p.
move: p => [p1 | p2].
move: p1 => [w1 [w2 [i [j k]]]].
exists (x::w1).
exists w2.
split.
rewrite -app_comm_cons.
rewrite -i.
done.
split. 
auto.
auto.

exists nil.
exists (x::w).
split.
done.
split.
apply contains0_ok.
done.
auto.
rewrite e in p.
simpl in p.
move: p => [w1 [w2 [i [j k]]]].
exists (x::w1).
exists w2.
split.
rewrite -app_comm_cons.
rewrite -i.
done.
split. 
auto.
auto.

+ move => p.
simpl in p.
move: p => [w1 [w2 [i [j [n k]]]]].
exists (1+n).
simpl.
exists (x::w1).
exists w2.
split.
rewrite -app_comm_cons.
rewrite i.
done.
split.
auto.
auto. 
Qed.


Lemma Brzozowski_correct (x : A) (w : word) (r : regexp) :
   interp (Brzozowski x r) w -> interp r (x :: w).
Proof.
apply Brzozowski_correct_aux.
Qed.


(* Q17. show that `rmatch` is correct.                                  *)

Lemma rmatch_RE_Empty (w : word):
  rmatch RE_Empty w -> False.
Proof.
induction w.
done.
simpl.
done.
Qed.

Lemma rmatch_RE_Void (w : word):
  rmatch RE_Void w -> w = nil.
Proof.
case w.
done.
simpl.
move => a l p.
have final: False -> (a :: l = nil).
done.
apply final.
apply rmatch_RE_Empty in p.
auto.
Qed.

Lemma rmatch_Union:
  forall w r1 r2, rmatch (RE_Union r1 r2) w = true -> rmatch r1 w = true \/ rmatch r2 w = true.
Proof.
induction w; move => r1 r2; try done.
move => p.
simpl.
simpl in p.
move/orP: p => p.
move: p => [p1 | p2].
left. done.
right. done.
move => p.
simpl in p.
simpl.
apply IHw.
done.
Qed.

Lemma rmatch_Concat:
  forall w r1 r2, rmatch (RE_Concat r1 r2) w = true -> exists w1 w2, w = w1 ++ w2 /\ rmatch r1 w1 /\ rmatch r2 w2.
Proof.
induction w; move => r1 r2; try done.
move => p.
exists nil.
exists nil.
split.
done.
simpl in p.
simpl.
move/andP: p => p.
done.
simpl.
case e: (contains0 r1).
move => p.
have i: rmatch (RE_Concat (Brzozowski a r1) r2) w \/ rmatch (Brzozowski a r2) w.
apply rmatch_Union.
done.
move: i => [i1 | i2].
have j1: exists w1 w2, w = w1 ++ w2 /\ rmatch (Brzozowski a r1) w1 /\ rmatch r2 w2.
apply IHw.
done.
move: j1 => [w1 [w2 h]].
move: h => [h1 [h2 h3]].
exists (a::w1).
exists w2.
split.
rewrite h1.
apply app_comm_cons.
split.
simpl.
done.
done.
exists nil.
exists (a::w).
split.
done.
split. 
simpl.
done.
simpl.
done.
move => p.
have j: (exists w1 w2, w = w1 ++ w2 /\ rmatch (Brzozowski a r1) w1 /\ rmatch r2 w2).
auto.
move: j => [w1 [w2 h]].
move: h => [h1 [h2 h3]].
exists (a::w1).
exists w2.
split.
rewrite h1.
apply app_comm_cons.
split.
simpl.
done.
done.
Qed.

Lemma rmatch_correct_aux (r : regexp):
  forall w, rmatch r w -> interp r w.
Proof.
induction r; move => w; case w; simpl; try done; try apply contains0_ok; simpl; try done.
+ move => a l p.
apply rmatch_RE_Empty in p.
done.
+  move => a l p.
have final: False -> lang1 (a :: l).
done.
apply final.
apply rmatch_RE_Empty with l.
done.
+ move => a0 l p.
simpl in p.
case e: (Aeq a0 a).
have j: a0 = a.
apply Aeq_dec.
done.
rewrite j.
rewrite e in p.
have k: l = nil.
apply rmatch_RE_Void.
done.
rewrite k.
done.
have final: False -> langA a (a0 :: l).
done.
rewrite e in p.
apply final.
apply rmatch_RE_Empty with l.
done.

+ move => p.
move/orP: p => p.
move: p => [p1 | p2].
left.
apply contains0_ok.
done.
right.
apply contains0_ok.
done.

+ move => a l p.
have e: rmatch (Brzozowski a r1) l = true \/ rmatch (Brzozowski a r2) l = true.
apply rmatch_Union.
done.
move: e => [e1 | e2].
left. auto.
right. auto.

+ move => p.
move/andP: p => p.
move: p => [p1 p2].
exists nil.
exists nil.
split.
done.
split.
auto.
auto.

+ move => a l.
case e: (contains0 r1).
move => p.
have f: rmatch (RE_Concat (Brzozowski a r1) r2) l = true \/ rmatch (Brzozowski a r2) l = true.
apply rmatch_Union.
done.
move: f => [f1 | f2].
have j: exists w1 w2, l = w1 ++ w2 /\ rmatch (Brzozowski a r1) w1 /\ rmatch r2 w2.
apply rmatch_Concat.
done.
move: j => [w1 [w2 [h1 [h2 h3]]]].
exists (a::w1).
exists w2.
split.
rewrite h1.
apply app_comm_cons.
split.
simpl.
apply IHr1.
simpl.
done.
auto.
exists nil.
exists (a::l).
split.
done.
split.
apply contains0_ok.
done.
apply IHr2.
simpl. auto.

move => p.
have j: exists w1 w2, l = w1 ++ w2 /\ rmatch (Brzozowski a r1) w1 /\ rmatch r2 w2.
apply rmatch_Concat.
done.
move: j => [w1 [w2 [h1 [h2 h3]]]].
exists (a::w1).
exists w2.
split.
rewrite h1.
apply app_comm_cons.
split.
simpl.
apply IHr1.
simpl.
done.
auto.

+ move => t.
destruct t.
exists 0.
done.

+ move => a l p.
have e: exists w1 w2, l = w1 ++ w2 /\ rmatch (Brzozowski a r) w1 /\ rmatch (RE_Kleene r) w2.
apply rmatch_Concat.
done.
move: e => [w1 [w2 [h1 [h2 h3]]]].


Admitted.






(* Q18. (HARD - OPTIONAL) show that `rmatch` is complete.               *)

Lemma rmatch_complete (r : regexp) (w : word):
  interp r w -> rmatch r w.

Proof. todo. Qed.

