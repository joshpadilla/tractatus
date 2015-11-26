# Problem Statement

The basic problem is: we want an abstract syntax such that

1. we want to match `λ x.x` with `λ y.y` (they're alpha congruent), 
2. blindly substituting terms into other terms should work, e.g.,
   substituting `λ x y.y z` into `λ w z . z w z` shouldn't have any
   naming collisions.

The naive approach (just have variables be strings) won't solve either
of these problems.

This isn't a new problem, it's been around for 40 years or so (if not
longer). There are at least half a dozen different approaches, 4 of the
most popular ones we'll discuss.

A good review of this subject:

- [Bound](https://www.fpcomplete.com/user/edwardk/bound)

Unfortunately, most of the tricks won't work in Coq, since the inductive
form is "negative" &mdash; this is bad for
[theoretical](http://cstheory.stackexchange.com/q/14415) and 
[practical](http://stackoverflow.com/q/12651146) reasons, in short
there's no guarantee the code will [terminate](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.Totality).

# De Bruijn Indices

The first approach is a "hack": the de Bruijn index
convention. Basically, variables are natural numbers indicating how
"deep" they're
bound. [Wikipedia](https://en.wikipedia.org/wiki/De_Bruijn_index) has a
decent introduction to the subject.

The main disadvantage that I see: the term `λ x y.y z` in De Bruijn
indices becomes `λλ(13)`. And `λ x y.y w` likewise evaluates to `λλ(13)`.
But `λ x y.y z` is not alpha congruent to `λ x y.y w`. That's the
problem I have with the naive De Bruijn index convention. The solution
is either (a) have some complicated scoping rules, or (b) have free
variables on different footing than bound variables (e.g., keep free
variables as strings but bound variables as natural numbers).

**Substitutions.** The trouble with de Bruijn indices lies in
substitution. It requires new formal framework for "shifting" the bound
variables. What does this mean? Well, suppose we had a simple combinator
in De Bruijn convention `K = λλ2` and `I=λ1`. Then `KI` would evaluate
to:

```haskell
(λx y . x) (λ z . z) -> (λ z y . z) = K
```

But how do we implement this in De Bruijn indices? The naive
substitution would give us

```haskell
(λλ2) (λ1) -> (λλ2).
```

Great! Lets try another. 

```haskell
(λ x y . w x (λ z . z x)) (λ t . u t) = (λ λ 4 2 (λ 1 3)) (λ 5 1)
                                      -> (λ 4 (λ 5 1) (λ 1 (λ 5 1)))
```

But now we need to decrement the free variables, or _shift_ the indices
after "plugging" in the "rand" to the "rator". The free variable in the
_rator_ will _decrease_ according to the depth, and the free variables
in the _rand_ will _increase_ according to its depth. So

```haskell
(λ 4 (λ 5 1) (λ 1 (λ 5 1))) -> (λ (4-1) (λ (5+1) 1) (λ 1 (λ (5+2) 1)))
                             = (λ 3 (λ 6 1) (λ 1 (λ 7 1)))
```

We have explicitly written out the shift in indices to make clear what
we're doing. _Observe: Bound Variables don't Shift._

This _shifty_ business can be formalized in a few abstract but rigorous
rules. The original paper on this is quite interesting in its own right:

- Martin Abadi, Luca Cardelli, Pierre-Louis Curien, Jean-Jacques Levy,
  [Explicit Substitutions](http://www.hpl.hp.com/techreports/Compaq-DEC/SRC-RR-54.pdf) (pdf), 72 pages.

Unfortunately, all proofs involving substitution are no longer as
intuitive as they once were...which is why people research alternatives
to the naive De Bruijn indices. To see an example of what a mess this
looks like, see:

- Andrej Bauer's [How to implement dependent type theory III](http://math.andrej.com/2012/11/29/how-to-implement-dependent-type-theory-iii/)
- Ben Lippmeier's [How I learned to stop worrying and love de Bruijn indices](http://disciple-devel.blogspot.com/2011/08/how-i-learned-to-stop-worrying-and-love.html)

**Implementation.** Arguably, this isn't too terrible. There's a great
implementation in Coq for untyped lambda calculus using De Bruijn
indices, see:

- [La Girafe Sportive](https://github.com/knuton/la-girafe-sportive)

# Locally Nameless Variables

So, how can we solve this problem? If we represent free variables using
strings, and bound variables as themselves, then we've got a way! How?
Well, we no longer have to shift upon substitution. After all, we only
had to shift the _free_ variables, so if we don't represent them with De
Bruijn indices, we're golden.

So in this scheme, we'd have
`(λ x y . w x (λ z . z x))` become `(λ λ w 2 (λ 1 3))`, and `(λ t . u
t)` would become `(λ u 1)`. Substitution simplifies drastically, keeping
track of the depth. What could go wrong?

Well, consider the term `λ 5`. This is not a valid locally nameless
term. The main trick appears to be to introduce formation rules to make
such constructions illegal, in a seemingly _post hoc_ manner.

- Arthur Charguéraud,
  [Locally nameless representation with cofinite quantification](http://www.chargueraud.org/softs/ln/)

# Parametric Higher Order Abstract Syntax

Well, we're programming in a language that has _already_ implemented
this stuff, so why not "punt" the problem to the metalanguage? This is
the scheme taken by Higher Order Abstract Syntax representations.

Although this sounds great (and, indeed, it is), it gives us everything
and the kitchen sink.

- Adam Chlipala,
  [Parametric Higher-Order Abstract Syntax for Mechanized Semantics](http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf)
  (pdf) 14 pages.
- Marc Bezem, Dimitri Hendriks, and Hans de Nivelle,
  [Automated Proof Construction in Type Theory using Resolution](http://www.phil.uu.nl/ozsl/articles/Hendriks01.pdf)
  (pdf) 26 pages.
