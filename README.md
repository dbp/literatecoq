## About

This is a library that intends to make it easier to write Coq proofs that more
closely match paper proofs. This means that there should be automation, as
manual proof scripts are impenetrable and fragile, but that hints should be
localized to individual proofs. It's quite new! Current features are the
following tactics:

```
hint lemma, lemma, ...
```

Adds given lemmas/theorems to hints for the current proof goal, to be used by
proof search.


```
hint_rewrite lemma, ...
```

Similarly, but the end is expected to be an equality, and it will be used for
left-to-right rewriting.

```
hint_rewrite <- lemma, ...
```

Like `hint_rewrite`, but for right-to-left rewriting.

```
hint_simpl
```

Ask proof automation to try running `simpl` (not sure how well this works yet).

```
hint_congruence
```

Ask proof automation to try running `congruence` (not sure how well this works yet).

```
hint_reflexivity
```

Ask proof automation to try running `reflexivity` (not sure how well this works yet).

```
iauto/iauto'
```

These are just wrappers for `try solve [intuition (eauto 3)]` and `try solve
[intuition eauto]`.

```
invert
```

Slightly better `inversion` -- clears the hypothesis and `subst`s.


```
simplify
```

Does some basic predicate logic stuff, removing obvious things, splitting
obvious things, etc.
