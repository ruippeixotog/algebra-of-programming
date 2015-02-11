## Solutions

### 1.1 (page 6)

The equation `f n = (f n) + 1` is not satisfied by any function.

### 1.2

No. The following two functions obey the recursion equation:
  * `m1 (x, y) = x + 1`;
  * `m2 (x, y) = if (x >= y) then (x + 1) else (y - 1)`.

### 1.3

```haskell
Nat+ ::= one | succ+ Nat+

foldn+ (c, h) one = c
foldn+ (c, h) (succ+ n) = h (foldn+ (c, h) n)

f zero = one
f (succ n) = succ+ (f n)

g one = zero
g (succ+ n) = succ (g n)
```

### 1.4

```haskell
sqr = f . foldn ((0, 1), h)
f (m, n) = m
h (m, n) = (m + n, n + 2)
```

### 1.5

```haskell
last p = f . foldn ((0, 0, p), h)
f (m, l, p) = l
h (m, l, p) = (m + 1, if (p 0, m, l), p)

if (true, then, else) = then
if (false, then, else) = else
```

### 1.6

```haskell
curry ack = foldn (succ, f)
curry ack x y = ack (x, y)

ack (x, y) = foldn (succ, f) x y
f fun =
```

[TODO] 

### 1.7 (page 14)

```haskell
convert = foldl (nilr, snocr)
```

### 1.8

```haskell
catconv: (listr A <- listr A) <- listl A

catconv = foldl (id, h)
h (accf, a) = accf . (curry cons a)

convert x = catconv x nil
```

### 1.9

Base case:

```
  nil ++ nil
=   {first equation defining ++}
  nil.
```

Induction step:

```
  nil ++ snoc (x, a)
=   {second equation defining ++}
  snoc (nil ++ x, a)
=   {induction hypothesis}
  snoc (x, a).
```

### 1.10

```haskell
cat x y = foldr (y, cons) x
```

### 1.11

```haskell
h: A <- (listr A, A)
hr: A <- (A, listr A)

foldl (c, h) x = foldr (id, hr h) x c
hr h (a, accf) = accf . (curryr h a)
curryr f c b = f (b, c)
```

### 1.12

```haskell
take n x = foldr (nilp, h) x n
h (a, accf) 0 = nil
h (a, accf) (n + 1) = cons (a, (accf n))

drop n x = foldr (nilp, f) x n
h (a, accf) 0 = cons (a, (accf n))
h (a, accf) (n + 1) = accf n
```

### 1.13 (page 16)

```haskell
foldg h (node (a, ts)) =
  h (a, listl (foldg h) ts)

size = foldg f
f a ts = (sum ts) + 1

depth (node (a, ts)) = foldg h
                       where h a ts = (maxl ts) + 1

max nil = 0
max (snoc (xs, a)) = bmax (maxl xs, a)
```

### 1.14

The expression is represented as:

```haskell
node ('f', [
  node ('g', [
    node ('a', nil),
    node ('b', nil)
  ]),
  node ('h', [
    node ('c', nil)
  ]),
  node ('d', nil)
])
```

The `curry` and `uncurry` functions are defined as:

```
curry = foldg h
        where h (a, ts) = foldl (tip a, bin) ts

uncurry = foldt (f, g)
          where f a = node (a, nil);
                g (left, node (b, ts)) = node (b, snoc (ts, left))
```

### 1.15 (page 18)

```haskell
zip = foldr (const nil, h)
      where h (a, accf) (cons (x, xs)) = cons ((a, x), accf xs)
```

### 1.16

```haskell
NonZero ::= 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
Digits ::= digits (NonZero, listl Digit)

foldd (f, h) (nz, ds) = foldl (f nz, h)

eval = foldd (id, h)
       where h (n, acc) = n + 10 * acc
```

We can specify `decimal` as inverse of `eval`, as `eval` is injective (no natural number has more than one way to be specified as `Digits`).

### 1.17 (page 19)

Proof that `listr f . concat = concat . listr (listr f)`:

* Base case:

```
  listr f . concat nil 
=   {definition of concat / first equation defining foldr}
  listr f nil
=   {first equation defining listr}
  nil
=   {definition of concat}
  concat nil
=   {first equation defining listr}
  concat . listr (listr f) nil.
```

* Induction step:

```
  listr f . concat (cons (x, xs))
=   {definition of concat / second equation defining foldr}
  listr f (cat (x, concat xs))
=   {definition of cat}
  listr f (x ++ concat xs)
=   {(missing) proof that listr f (x ++ y) = (listr f x) ++ (listr f y)}
  (listr f x) ++ (listr f . concat xs)
=   {induction hypothesis}
  (listr f x) ++ (concat . listr (listr f) xs)
=   {definition of cat}
  cat (listr f x) (concat . listr (listr f) xs)
=   {definition of concat / second euqation defining foldr}
  concat (cons (listr f x, listr (listr f) xs))
=   {second equation defining listr}
  concat listr (listr f) (cons (x, xs)).
```

Proof that `listl (listl f) . inits = inits . listl f`:

* Base case:

```
  listl (listl f) . inits nil
=   {definition of inits / first equation defining foldl}
  listl (listl f) [nil]
=   {first equation defining listl}
  [nil]
=   {definition of inits / first equation defining foldl}
  inits nil
=   {first equation defining listl}
  inits . listl f nil.
```

* Induction step:

```
  listl (listl f) . inits (snoc (xs, x))
=   {definition of inits / second equation defining foldl}
  listl (listl f) fa (inits xs, x)
  listl (listl f) (snoc (snoc (xss, xsx), snoc (xss, a)))
```

[TODO]

Proof that `listr f . reverse = reverse . listr f`:

* Base case:

```
  listr f . reverse nil
=   {definition of reverse / first equation defining foldr}
  listr f nil
=   {first equation defining listr}
  nil
=   {definition of reverse / first equation defining foldr}
  reverse nil
=   {first equation defining listr}
  reverse . listr f nil.
```

* Induction step:

```
  listr f . reverse (cons (x, xs))
=   {definition of reverse / second equation defining foldr}
  listr f (append (x, reverse xs))
=   {definition of append}
  listr f (snocr (reverse xs, x))
=   {(missing) proof that snocr is a natural transformation}
  snocr (listr f . reverse xs, f x)
=   {induction hypothesis}
  snocr (reverse . listr f xs, f x)
=   {definition of append}
  append (f x, reverse . listr f xs)
=   {definition of reverse / second equation defining foldr}
  reverse (cons (f x, listr f xs))
=   {second equation defining listr}
  reverse . listr f (cons (x, xs)).
```

Proof that `listr (cross (f, g)) . zip = zip . cross (listr f, listr g)`:

* Base case:

```
  listr (cross (f, g)) . zip (nil, nil)
=   {first equation defining zip}
  listr (cross (f, g)) nil
=   {first equation defining listr}
  nil
=   {first equation defining zip}
  zip (nil, nil)
=   {definition of cross / first equation defining listr}
  zip . cross (listr f, listr g) (nil, nil).
```

* Induction step:

```
  listr (cross (f, g)) . zip (cons (x, xs), cons (y, ys))
=   {second equation defining zip}
  listr (cross (f, g)) (cons ((x, y), zip (xs, ys)))
=   {second equation defining listr}
  cons (cross (f, g) (x, y), listr (cross (f, g)) . zip (xs, ys))
=   {induction hypothesis}
  cons (cross (f, g) (x, y), zip . cross (listr f, listr g) (xs, ys))
=   {definition of cross}
  cons ((f x, g y), zip . cross (listr f, listr g) (xs, ys))
=   {second equation defining zip}
  zip . cons ((f x, g y), cross (listr f, listr g) (xs, ys))
=   {definition of cross / second equation defining listr}
  zip . cross (listr f, listr g) (cons (x, xs), cons (y, ys)).
```

### 1.18

The equality is `tree (cross (f, g)) . foo = foo . cross (listr f, listr g)`.

### 1.19

The equality is `listl f . foo = foo . gtree f`, where `gtree f` is the map function for general trees, the datatype introduced in exercise 1.13.
