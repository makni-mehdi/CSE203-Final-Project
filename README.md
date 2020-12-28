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
```
