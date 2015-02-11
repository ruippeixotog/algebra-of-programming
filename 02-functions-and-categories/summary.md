## Categories

A category is a set of objects and arrows from an object to another.

### Composition properties

  * Associativity of composition: f . (g . h) = (f . g) . h
  * Identity as unit of composition: id<sub>A</sub> . f = f = f . id<sub>B</sub>

### Arrow properties

  * An arrow m is monic iff:  f = g  ≡  m . f = m . g
  * An arrow e is epic iff: f = g  ≡  f . e = g . e
  * An arrow i is an isomorphism iff: ∃j : j . i = id<sub>B</sub> ∧ i . j = id<sub>A</sub>

### Opposite category and duality

  * f . g in C<sup>op</sup> = g . f in C
  * Let S(C) be a statement about C: (∀C : S(C)) ≡ (∀C : S<sup>op</sup>(C))

## Functors

A functor is a mapping between two categories. It consists of a mapping from objects to objects and another from arrows to arrows.

### Required properties

  * Ff : FA ← FB whenever f: A ← B
  * Functors preserve identities: F(id<sub>A</sub>) = id<sub>FA</sub>
  * Functors preserve composition: F(f . g) = Ff . Fg

### Examples

  * Identity functor id: C ← C
    * id(A) = A
    * id(f) = f
  * Constant functor K<sub>B</sub>: C ← D, where B is an object of C
    * K<sub>B</sub>A = B
    * K<sub>B</sub>f = id<sub>B</sub>
  * Squaring functor (_)<sup>2</sup>: Fun ← Fun
    * A<sup>2</sup> = { (a, b) | a ∈ A, b ∈ A }
    * f<sup>2</sup> (a, b) = (f a, f b)
  * Powerset functor P: Fun ← Fun
    * PA = { x | x ⊆ A }
    * Pf applies f to all elements of a given set
  * Existential image functor E: Fun ← Rel
    * EA = PA
    * (ER) x = { a | (∃b : aRb ∧ b ⊆ x) }

## Natural transformations

A transformation from the functor G to the functor F is a collection of arrows ϕ<sub>B</sub>: FB ← GB, one for each object B - the components of ϕ. A transformation is natural iff Fh . ϕ<sub>B</sub> = ϕ<sub>A</sub> . Gh.

[TODO diagram]

## Terminal objects

A terminal object of a category C is an object T such that for each object A of C there is exactly one arrow T ← A. The terminal object is named 1 and the unique arrow from A to 1 is written !<sub>A</sub>. Any two terminal objects are isomorphic.

### Universal property

  * h = !<sub>A</sub> ≡ h: 1 ← A

### Laws

  * Reflection law: !<sub>1</sub> = id<sub>1</sub>
  * Fusion law: !<sub>A</sub> . f = !<sub>B</sub> <= f: A ← B

### Examples

  * In Fun, the terminal object is a singleton set {p} and !<sub>A</sub> is the constant function that maps every element of A to p;
  * In Par and Rel the terminal object is the empty set and !<sub>A</sub> is the empty relation ∅.

## Initial objects

An initial object of C is a terminal object of C<sup>op</sup>. Thus, I is initial if for each object A of C there is exactly one arrow of type A ← I. The initial object is named 0 and the unique arrow from 0 to A is written ¡<sub>A</sub>. Any two initial objects are isomorphic.

### Universal property

  * h = ¡<sub>A</sub> ≡ h: A ← 0

### Laws

  * Reflection law: ¡<sub>0</sub> = id<sub>0</sub>
  * Fusion law: f . ¡<sub>A</sub> = ¡<sub>B</sub> <= f: B ← A

### Examples

  * In Fun, the initial object is the empty set and ¡<sub>A</sub> is the empty function;
  * In Par and Rel the initial object is also the empty set and ¡<sub>A</sub> is the empty relation ∅.

## Products

A product of two objects A and B consists of an object and two arrows. The object is written as A x B and the arrows are written outl: A ← A x B and outr B ← A x B. The three elements are required to satisfy the following property: for each pair of arrows f: A ← C and g: B ← C there exists an arrow 〈f, g〉: A x B ← C such that the property below holds.

### Universal property

  * h = 〈f, g〉 ≡ outl . h = f and outr . h = g

### Laws

  * Cancellation property: outl . 〈f, g〉 = f and outr . 〈f, g〉 = g
  * Reflection law: 〈outl, outr〉 = id
  * Fusion law: 〈h, k〉 . m = 〈f, g〉 <= h . m = f and k . m = g
    * Alternatively: 〈h, k〉 . m = 〈h . m, k . m〉

### Functor

In each pair of objects in C has a functor, one says that C "has products". In such a case, x can be made into a functor C ← C x C:

  * f x g = 〈f . outl, g . outr〉
  * Functor composition: (f x g) . (h x k) = (f . h) x (g . k)
  * Absorption law: (f x g) . 〈p, q〉 = 〈f . p, g . q〉

## Coproducts

The product of A and B on C<sup>op</sup> is called the coproduct of A and B in C. Thus coproducts, like products, also consist of one object and two arrows for each A and B. The object is denoted A + B and the two arrows by inl: A + B ← A and inr: A + B ← B. The unique arrow C ← A + B is written [f, g].

### Universal property

  * h = [f, g] ≡ h . inl = f and h . inr = g

### Laws

  * Cancellation property: [f, g] . inl = f and [f, g] . inr = g
  * Reflection law: [inl, inr] = id
  * Fusion law: m. [h, k] = [f, g] <= m . h = f and m . k = g
    * Alternatively: m . [h, k] = [m . h, m . k]
  * Exchange law (exercise 2.27): 〈[f, g], [h, k]〉 = [〈f, h〉, 〈g, k〉]

### Functor

  * f + g = [inl . f, inr . g]
  * Functor composition: (f + g) . (h + k) = f . h + g . k
  * Absorption law: [f, g] . (h + k) = [f . h, g . k]

## Useful arrows

In any category with a terminal object and products, there exist natural isomorphisms (exercise 2.26):

  * unit: A ← A x 1
  * swap: A x B ← B x A
  * assocr: A x (B x C) ← (A x B) x C

## F-algebras

[TODO]

### F-homomorphisms

[TODO]

### Initial F-algebra

### Catamorphisms

[TODO]

### Examples

[TODO]

  * Natural numbers:
  * Strings:

## Type functors

[TODO]
