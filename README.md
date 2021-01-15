# CSE203-Final-Project
Formally defining languages, regular languages and regular expressions and proving multiple Lemmas about them.

## Some important lemmas

```
Lemma concat0L L : langS lang0 L =L lang0.
Lemma concatL0 L : langS L lang0 =L lang0.
Lemma concat1L L : langS lang1 L =L L.
Lemma concatL1 L : langS L lang1 =L L.
Lemma concatA L G H : langS (langS L G) H =L langS L (langS G H).
Lemma unionC L G : langU L G =L langU G L.
Lemma interC L G : langI L G =L langI G L.
Lemma eqL_concat_l L G W: L =L G -> langS W L =L langS W G.
Lemma eqL_concat_r L G W: L =L G -> langS L W =L langS G W.
Lemma langKn_app : forall n m L, langS (langKn L n) (langKn L m) =L langKn L (n + m).
Lemma langKK L : langK (langK L) =L langK L.

Lemma eqL_word_concat a w : langW (a::w) =L (langS (langA a) (langW w)).
Lemma eqL_commutative L G: L =L G -> G =L L.
Lemma eqL_transitive L G W: L =L G -> G =L W -> W =L L.
Lemma langKn_langS L n: langS L (langKn L n) =L langS (langKn L n) L.
Lemma langM_langS L G: langS (langM L) (langM G) =L langM (langS G L).
Lemma langKn_langM L n: langKn (langM L) n =L langM (langKn L n).

Lemma eqL_langU L1 G1 L2 G2 : (L1 =L L2) /\ (G1 =L G2) -> langU L1 G1 =L langU L2 G2.
Lemma eqL_langS L1 G1 L2 G2 : (L1 =L L2) /\ (G1 =L G2) -> langS L1 G1 =L langS L2 G2.
Lemma eqL_langKn L1 L2 n: L1 =L L2 -> langKn L1 n =L langKn L2 n.
Lemma eqL_langK L1 L2: L1 =L L2 -> langK L1 =L langK L2.
Lemma langKn_imply L G n: (forall w, L w -> G w) -> (forall w, langKn L n w -> langKn G n w).
Lemma langK_imply L G: (forall w, L w -> G w) -> (forall w, langK L w -> langK G w).
Lemma union_kleene (r1 r2: regexp) : RE_Kleene(RE_Union r1 r2) ~ RE_Kleene(RE_Concat(RE_Kleene r1)(RE_Kleene r2)).
Lemma contains0_ok r : contains0 r <-> interp r nil.
Lemma Brzozowski_correct_aux (x : A) (r : regexp) : forall w, interp (Brzozowski x r) w -> interp r (x :: w).
Lemma Brzozowski_correct (x : A) (w : word) (r : regexp) : interp (Brzozowski x r) w -> interp r (x :: w).
Lemma rmatch_correct_aux (w: word): forall r, rmatch r w -> interp r w.
Lemma rmatch_correct (w: word) (r: regexp): rmatch r w -> interp r w.
Lemma app_inj_head: forall a b (x y: list A), a::x = b::y -> a = b /\ x = y.
Lemma Brzozowski_correct_aux2 (x : A) (r : regexp) : forall w, interp r (x :: w) -> interp (Brzozowski x r) w.
Lemma Brzozowski_correct2 (x : A) (w : word) (r : regexp) : interp r (x :: w) -> interp (Brzozowski x r) w.
Lemma rmatch_complete_aux (w : word): forall r, interp r w -> rmatch r w.
Lemma rmatch_complete (r: regexp) (w : word): interp r w -> rmatch r w.
```
