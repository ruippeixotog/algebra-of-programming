## Solutions

### 3.1 (page 56)

```
  〈[zero, plus] . Foutl, [zero, succ . outr] . Foutr〉 = [zeros, pluss]
≡  {product fusion}
  〈[zero . Foutl, plus . Foutl], [zero . Foutr, succ . outr . Foutr]〉 = [zeros, pluss]
≡  {exchange law (exercise 2.27)}
  [〈zero . Foutl, zero . Foutr〉, 〈plus . Foutl, succ . outr . Foutr〉] = [zeros, pluss]
≡  {definition of zero}
  [〈zero, zero〉, 〈plus . Foutl, succ . outr . Foutr〉] = [zeros, pluss]
≡  {universal property of coproducts}
  〈zero, zero〉 = zeros ∧ 〈plus . Foutl, succ . outr . Foutr〉 = pluss
≡  {definition of zeros and pluss}
  true ∧ 〈plus . Foutl, succ . outr . Foutr〉 = 〈plus . 〈outl, outl . outr〉, succ . outr . outr〉
≡  {universal property of products}
  plus . Foutl = plus . 〈outl, outl . outr〉 ∧ succ . outr . Foutr = succ . outr . outr
≡  {definition of F}
  plus . (id x outl) = plus . 〈outl, outl . outr〉 ∧ succ . outr . (id x outr) = succ . outr . outr
≡  {definiton of product functor, product cancellation law}
  true ∧ true.
```

### 3.2

`Foutl: FA <- F(A x B)` and `Foutr: FB <- F(A x B)`; therefore, `φ: (FA x FB) <- F(A x B)` for all `A` and `B`. The proof that `φ` is a natural transformation is:

```
  (Ff x Fg) . φ = φ . F(f x g)
≡  {definition of φ}
  (Ff x Fg) . 〈Foutl, Foutr〉 = 〈Foutl, Foutr〉 . F(f x g)
≡  {product absorption and fusion law}
  〈Ff . Foutl, Fg . Foutr〉 = 〈Foutl . F(f x g), Foutr . F(f x g)〉
≡  {functor composition}
  〈F(f . outl), F(g . outr)〉 = 〈F(outl . (f x g)), F(outr . (f x g))〉
≡  {universal property of products}
  F(f . outl) = F(outl . (f x g)) ∧ F(g . outr) = F(outr . (f x g))
≡  {outl and outr are natural transformations, functors preserve transformations}
  true.
```

### 3.3

```haskell
steep xs = outl . steepr xs
steepr nil = 〈true, 0〉
steepr (cons (a, x)) = 〈f a, g a〉 . steepr x
                       where f a (res, sum) = res ∧ a > sum
                       where g a (res, sum) = plus (a, sum)
```

### 3.4

As `(|k|)` is a capamorphism, `k: (A x B) <- F(A x B)`. The diagram that represents the types in this exercise is:

[TODO diagram]

The diagram implies that `(|k|) = 〈f, (|h|)〉`. From here:

```
  〈f, (|h|)〉 = (|k|)
≡  {universal property of catamorphisms}
  k . F〈f, (|h|)〉 = 〈f, (|h|)〉 . α
≡  {product fusion law}
  k . F〈f, (|h|)〉 = 〈f . α, (|h|) . α〉
≡  {initial premise}
  k . F〈f, (|h|)〉 = 〈g . F〈f, (|h|)〉, (|h|) . α〉
≡  {universal property of catamorphisms}
  k . F〈f, (|h|)〉 = 〈g . F〈f, (|h|)〉, h . F(|h|)〉
≡  {product cancellation property, F functor}
  k . F〈f, (|h|)〉 = 〈g . F〈f, (|h|)〉, h . Foutr . F〈f, (|h|)〉〉
≡  {product fusion law}
  k . F〈f, (|h|)〉 = 〈g, h . Foutr〉 . F〈f, (|h|)〉
<= {function application}
  k = 〈g, h . Foutr〉.
```

### 3.5

Using the diagram of exercise 3.4:

* `A = Bool`;
* `B = Nat x Nat`, `(|h|) = [zero, size]`;
* `g (bal, (n, m)) = bal ∧ (1/3 <= n / (n + m + 1) <= 2/3)`;
* `h = [zero, size]`, where `size (l, e, r) = l + r + 1`.

THe resulting program is:

```haskell
balanced = outl · (|(true, zero), f|)
           where f ((lbal, n), e, (rbal, m)) = (g (lbal ∧ rbal, (n, m)), size (n, e, m))
```

### 3.6

[TODO derivation?]

```
preds = outl . (|(nil, zero), f|)
        where f (list, n) = (cons(succ n, list), succ n)
```

### 3.7

[TODO derivation?]

```
product = (|one, mult|)

fact = outl . (|(one, zero), f|)
       where f (res, n) = (mult (succ n, res), succ n)
```

### 3.8

```
  〈f, g〉 = (|〈h, k〉|)
≡  {universal property of catamorphisms}
  〈f, g〉 . α = 〈h, k〉 . F〈f, g〉
≡  {product fusion law}
  〈f . α, g . α〉 = 〈h . F〈f, g〉, k . F〈f, g〉〉
≡  {universal property of products}
  f . α = h . F〈f, g〉 and g . α = k . F〈f, g〉.
```

The banana-split law is the case where:
* `f = (|l|)`;
* `g = (|m|)`;
* `h = l . Foutl`;
* `k = m . Foutr`.

Exercise 3.4 is the case where, given arrows `l: B <- FB` and `m: B <- F(A x B)`:
* `f = outl . (|〈m, l . Foutr〉|)`;
* `g = (|l|)`;
* `h = m`;
* `k = (|l|) . Foutr`.

### 3.9 (page 61)

slice = tri drop

### 3.10

The direct definition of the hyperproduct function `hyper` is `hyper = product . tri square = (|succ . zero, mult|) . tri square`, where `square a = mult (a, a)`.

In order to apply Horner's rule, we need to prove that `square . [succ . zero, mult] = [succ . zero, mult] . (square + square x square)`:

```
  square . [succ . zero, mult] = [succ . zero, mult] . (square + square x square)
≡  {coproduct fusion law and functor}
  [square . succ . zero, square . mult] = [succ . zero . square, mult . (square x square)]
≡  {definition of square, zero as constant function}
  [succ . zero, square . mult] = [succ . zero, mult . (square x square)]
≡  {universal property of coproducts}
  succ . zero = succ . zero ∧ square . mult = mult . (square x square)
≡  {multiplication is associative}
  true.
```

Applying Horner's rule:

```
  (|succ . zero, mult|) . tri square
=  {Horner's rule}
  (|[succ . zero, mult] . (id + square x square)|)
=  {coproduct functor}
  (|succ . zero, mult . (square x square)|)
=  {since square . mult = mult . (square x square)}
  (|succ . zero, square . mult|).
```

### 3.11

The diagram is the same of the one in page 59, with an extra arrow `h: A <- A`. The proof of this generalization is identical to the one used to prove Horner's rule itself, replacing `f` for `h` where adequate.

### 3.12

The application of the rule in exercise 3.11 in polynomial evaluation, the pre-condition required for `h` is that `h . [zero, plus] = [zero, plus] . (id + f x h)`, where `f a = mult (a, x)`. Simplifying the condition, we obtain:

```
  h . [zero, plus] = [zero, plus] . (id + f x h)
≡  {coproduct fusion law and functor}
  [h . zero, h . plus] = [zero, plus . (f x h)]
≡  {universal property of coproducts}
  h . zero = zero ∧ h . plus = plus . (f x h).
```

Translating to mathematical notation, `h` must be such that:

* h(0) = 0;
* for any a and b, h(a + b) = f(a) + h(b).

Therefore, `h(a) = h(a + 0) = f(a) + h(0) = f(a)`, which means that `h` can only be equal to `f`.

### 3.13

The required expression is computed by `sum . listr mult . tri (succ x id) . listr 〈zero, id〉`. It first maps each element to a pair containing zero and itself. It then uses `tri` to transform each zero into the zero-based index of the element in the list. Finally, it maps each resulting pair to its element multiplication and sums all the elements.

### 3.14

The required program is `(|mult, plus|) . tri (succ x id) . tree <zero, id>`.

Applying Horner's rule:

```
  (|mult, plus|) . tri (succ x id) . tree <zero, id>
=  {Horner's rule}
  (|[mult, plus] . (id + (succ x id) x (succ x id))|) . tree <zero, id>
```

[TODO]

### 3.15 (page 65)

It is valid to take a `Decimal` as a `listr Digit` because there is an isomorphism between them.

We first note that `plus (a, b) / 10 = plus (a / 10, b / 10)`, a condition necessary for applying the Horner's rule:

```
  sum . tri (/10) . listr (/10)
=  {definition of sum}
  (|zero, plus|) . tri (/10) . listr (/10)
=  {Horner's rule}
  (|[zero, plus] . (id + id x (/10))|) . listr (/10)
=  {coproduct functor}
  (|zero, plus (id x (/10))|) . listr (/10)
=  {type functor fusion, coproduct functor}
  (|zero, plus (id x (/10)) . ((/10) x id)|)
=  {product functor}
  (|zero, plus ((/10) x (/10))|)
=  {definition of shift}
  (|zero, shift|).
```

### 3.16

If 2^2 was used, the only decimals representable were 0 (0/4), 0.25 (1/4), 0.5 (2/4), 0.75 (3/4) and 1 (4/4).

### 3.17

The proof is available in http://link.springer.com/chapter/10.1007/978-1-4612-4476-9_28, second page of "Look inside" preview.

### 3.18

For the purpose of contradiction, let `m = n` such that `k <= m ≢ k <= n` for any `k`. This leads to `k <= m ≢ k <= m`, which is a contradiction. Therefore, the given rule is proven true.

### 3.19

```
  n <= ⌊(a + r) / b⌋
≡  {property of floor}
  n <= (a + r) / b
≡
  n * b - a <= r
≡  {property of floor, as n * b - a is an integer}
  n * b - a <= ⌊r⌋
≡
  n <= (a + ⌊r⌋) / b
≡  {property of floor}
  n <= ⌊(a + ⌊r⌋) / b⌋
≡  {indirect equality using the first and the last expressions}
  ⌊(a + r) / b⌋ = ⌊(a + ⌊r⌋) / b⌋.
```

### 3.20

`⌊(0.5 + 0.5) / 1⌋ = 1`, while `⌊(0.5 + ⌊0.5⌋) / 1⌋ = 0`.

### 3.21

As `f` is injective, `f a = f b ≡ a = b` for all `a` and `b`. Therefore:

[TODO]

### 3.22

As `round` multiplies its decimal argument by 2^16 (65536) and then floors it, we're looking for two different arguments for `round` that are sufficient small such that they differ by less than one after multiplied: `round . val [0,0,0,0,0,1] = round . val [0,0,0,0,0,2] = 0`, while [TODO]

### 3.23 (page 69)

It is possible with `null = outr` and `unnull = <¡, id>`:

```
  <¡, id> . outr
=  {product fusion law, identity as unit of composition}
  <¡ . outr, outr>
=  {premise}
  <outl, outr>
=  {product reflection law}
  id.
```

```
  outr . <¡, id>
=  {product cancellation property}
  id.
```

### 3.24

No. As in `Rel` products and coproducts are the disjoint union of the two arguments, `(A x B) + (A x C) = A + B + A + C` and `A x (B + C) = A + B + C`. As `A + B + A + C != A + B + C`, `Rel` is not a distributive category.

### 3.25

We first prove that `(! + !) . distr = (! + !) . outr`:

```
  (! + !) . distr
=  {terminal object fusion}
  ((! . f) + (! . g)) . distr
=  {coproduct functor}
  (! + !) . [inl . f, inr . g] . distr
=  {take f = g = outr}
  (! + !) . [inl . outr, inr . outr] . distr
=  {outr as natural transformation}
  (! + !) . [outr x (id x inl), outr . (id x inr)] . distr
=  {coproduct fusion}
  (! + !) . outr . [id x inl, id x inr] . distr
=  {definition of undistr}
  (! + !) . outr . undistr . distr
=  {since undistr . distr = id}
  (! + !) . outr.
```

Then, we prove that (_)? is an isomorphism with inverse (_)¿, which in `Fun` implies that (_)? is injective:

```
  (p?)¿
=  {definitions of (_)? and (_)¿}
  (! + !) . (unit + unit) . distr . <id, p>
=  {coproduct functor}
  ((! . unit) + (! + unit)) . distr . <id, p>
=  {terminal object fusion law}
  (! + !) . distr . <id, p>
=  {previous proof}
  (! + !) . outr . <id, p>
=  {product cancellation property}
  (! + !) . p
=  {terminal object reflection law}
  p.
```

### 3.26

As `distr`, `unit`, `inl` and `inr` are all natural transformations, `(unit + unit) . distr` is also a natural transformation by composition, as depicted in the diagram below:

[TODO diagram]

### 3.27

`h` is an isomorphism by the definition of initial object (with `h^-1 = ¡`). As initial objects are unique up to unique isomorphism, `A` is also an initial object.

### 3.28

```
  f x [g, h]
=  {since undistr . distr = id}
  (f x [g, h]) . undistr . distr
=  {definition of undistr}
  (f x [g, h]) . [id x inl, id x inr] . distr
=  {coproduct fusion law}
  [(f x [g, h]) . (id x inl), (f x [g, h]) . (id x inr)] . distr
=  {product functor composition}
  [f x ([g, h] . inl), f x ([g, h] . inr)] . distr
=  {coproduct cancellation property}
  [f x g, f x h] . distr.
```

### 3.29

It is possible to define an isomorphism between every pair of objects in `Fun` with the same cardinality. As the size of `1 + 1 + 1 + 1` is 4 and the size of `Bool^2 = (1 + 1) x (1 + 1)` is also 4, a direct translation can be formed.

### 3.30

```
  filter p = listr f
≡  {definition of filter}
  concat . listr (p -> wrap, nil) . listr f
≡  {listr functor composition}
  concat . listr ((p -> wrap, nil) . f)
≡  {property 3.4 of conditional}
  concat . listr (p . f -> wrap . f, nil . f)
≡  {wrap as natural transformation, definition of nil}
  concat . listr (p . f -> listr f . wrap, nil)
≡  {definition of nil and listr}
  concat . listr (p . f -> listr f . wrap, listr f . nil)
≡  {property 3.3 of conditional}
  concat . listr (listr f . (p . f -> wrap, nil))
≡  {listr functor composition}
  concat . listr (listr f) . listr (p . f -> wrap, nil)
≡  {concat as natural transformation}
  listr f . concat . listr (p . f -> wrap, nil)
≡  {definition of filter}
  listr f . filter (p . f).
```

### 3.31 (page 75)

```
  cat ([nil, cons] x id) = [outr, cons] . (id + id x cat) . (id + assocr) . distl
≡  {functor composition}
  cat ([nil, cons] x id) = [outr, cons] . (id + ((id x cat) . assocr)) . distl
≡  {coproduct absorption law}
  cat ([nil, cons] x id) = [outr, cons . (id x cat) . assocr] . distl
≡  {application of undistl}
  cat ([nil, cons] x id) . undistl = [outr, cons . (id x cat) . assocr] . distl . undistl
≡  {definition of undistl; distl . undistl = id}
  cat ([nil, cons] x id) . [inl x id, inr x id] = [outr, cons . (id x cat) . assocr]
≡  {coproduct fusion law}
  cat [([nil, cons] x id) . (inl x id), ([nil, cons] x id) . (inr x id)] = [outr, cons . (id x cat) . assocr]
≡  {product functor composition, coproduct cancellation property}
  cat [nil x id, cons x id] = [outr, cons . (id x cat) . assocr]
≡  {coproduct universal and cancellation property}
  cat (nil x id) = outr ∧ cat (cons x id) = cons . (id x cat) . assocr.
```

### 3.32

[TODO]

### 3.33

For `A^0` and `1`, the functions `f = 1 <- A^0` and `f^-1: A^0 <- 1` are:

  * `f = !`;
  * `f^-1 = curry (¡ . outr)`.

For `A^1` and `A`, the functions `f = A <- A^1` and `f^-1: A^1 <- A` are:

  * `f = apply <id, !>`;
  * `f^-1 = curry outl`.

For `A^(B+C)` and `A^B x A^C`, the functions `f = A^B x A^C <- A^(B+C)` and `f^-1: A^(B+C) <- A^B x A^C` are:

  * `f = <curry (apply . (id x inl)), curry (apply . (id x inr))>`;
  * `f^-1 = curry ([apply . (outl x id), apply . (outr x id)] . distr)`.

[TODO add proofs that f . f^-1 = id = f^-1 . f]

### 3.34

Each arrow `f: A <- B` can be associated to the arrow `curry <!, f>: A^B <- 1`.

### 3.35

[TODO]

### 3.36

The mapped function `f: C <- A` should take a function object `A^B` to a object `C^B` in which `f` is applied after applying `C^B`. The mapping is therefore `f^B = curry (f . apply)`.

### 3.37

[TODO]

### 3.38

`map` is a natural transformation from the bifunctor `F(A, B) = A^B` to the bifunctor `G(A, B) = F(listr A, listr B) = (listr A)^(listr B)`, where `f^g = curry (f . apply . (id x g))`, with `f: C <- A` and `g: B <- D`, has type `f^g: C^D <- A^B`.

In the following proof, using the same technique as in the statement, objects `A^B` are implicitly viewed as arrows `A <- B`. In that form, `map h = listr h` and `F(f, g) h = f . h . g`.

```
  map . F(f, g) h = G(f, g) . map h
≡  {definition of G}
  map . F(f, g) h = F(listr f, listr g) . map h
≡  {h: A^B as A <- B}
  listr (f . h . g) = listr f . listr h . listr g
≡  {listr functor composition}
  listr (f . h . g) = listr (f . h . g).
```

### 3.39

By steps:

  * `id: A x B <- A x B`;
  * `curry id: (A x B)^B <- A`;
  * `map . curry id: (listr (A x B))^(listr B) <- A`;
  * `cpr = uncurry (map . curry id): listr (A x B) <- A x listr B`.
