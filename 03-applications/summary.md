## Distributive categories

In any category with products, coproducts and an initial object there are the following natural transformations:
  * undistr: A x (B + C) <- (A x B) + (A x C)
    * given by undistr = [id x inl, id x inr]
  * unnull: A x 0 <- 0

A category is distributive iff:

  * undistr is a isomorphism, meaning that there is an inverse arrow distr: (A x B) + (A x C) <- A x (B + C);
  * unnull is also an isomorphism, meaning that there is an inverse arrow null: 0 <- A x 0.

## Conditionals

[TODO]

## (TODO)

  * distl: (A x C) + (B x C) <- (A + B) x C

## Exponential objects and currying

Let C be a category with terminal object and products. An exponential of two objects A and B is an object A<sup>B</sup> and an arrow apply: A ← A<sup>B</sup> x B such that for each f: A ← C x B there is a unique arrow curry f: A<sup>B</sup> ← C such that the property below holds.

The inverse transformation of curry can be referred to as uncurry g: A ← C x B, defined for each arrow g: A<sup>B</sup> ← C.

### Universal property

  * g = curry f ≡ apply . (g x id) = f

### Laws

  * Reflection law: curry apply = id
  * Fusion law: curry f . g = curry (f . (g x id))

### Cartesian closed categories

If a category has finite products and for every pair of objects A and B the exponential A<sup>B</sup> exists, the category is said to be cartesian closed.

Set membership: ⊆
Exists: ∃
Forall: ∀
And: ∧
Phi: ϕ
Null: ∅
Inverted !: ¡
Products: 〈 〉
