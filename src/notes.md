A interesting problem comes form Giarrusso et al.'s paper: What happens if APIs contains higher-orderness? 

An illustrative example is:
```
singleton :: a -> Sequence a 
map :: (a -> b) -> Sequence a -> Sequence b 
concat :: Sequence (Sequence a) -> Sequence a
empty :: Sequence a 
```
which is used to define 

```
cartesianProd :: Sequence a -> Sequence b -> Sequence (a, b) 
cartesianProd xs ys = 
  concatMap (\a -> map (\b -> (a, b)) ys) xs 

concatMap f = concat . map f 
```

## 2nd-Order Abstract Syntax 

We can view `map` as a 2nd-order construct (i.e., construct with binders), and unembedding works well with binders. For example, we can view `map` as a special language construct that have:

    Γ |- e' : Sequence a
    Γ, x : a |- e : b 
    -------------------------------
    Γ |- map (x. e) e' : Sequence b

Recall that we interpret terms-in-context `Γ |- e : A` as 

    ∃C. (Γ -> A × C) × (ΔΓ × C -> ΔA × C) 

Then, our task is: 

    ∃C. (Γ -> Sequence A × C) × (ΔΓ × C -> Δ(Sequence A) × C) 
    ∃C. (Γ × A -> B × C) × (ΔΓ × ΔA × C -> ΔB × C)
    -----------------------------------------------------------
    ∃C. (Γ -> Sequence B × C) × (ΔΓ × C -> Δ(Sequence B) × C) 

The definition fo this API depends on a concrete definition of Δ(Sequence a), but with appropriate definitions of them, we can give one. 


Also, we can handle 2nd order APIs, which would be useful for the uses cases discussed by Giarrusso et al.'s (**Really?**). 

### Note on Aug 6. 

    (Γ -> Sequence A × C1) × (ΔΓ × C1 -> Δ(Sequence A) × C1) 
    (Γ × A -> B × C2) × (ΔΓ × ΔA × C2 -> ΔB × C2)
    -----------------------------------------------------------
    ∃C. (Γ -> Sequence B × C) × (ΔΓ × C -> Δ(Sequence B) × C) 

Having this function is possible; to do so we will take Γ × C1 × Sequence C2. 
Γ is required as we need to run a function of type `A -> B × C2`. We collect the produced C2 to make `Sequence C2`. 

---

~~**Note on Aug 18, 2021** I realized that the story is not that simple. Consider the case where we obtain the identity change for `Δ(Sequence A)` part, whereas `ΔΓ` is not the identity change---this actually can happen for the `cartesianProd as bs` above when the change to `as` is the identity update.~~ 

~~So, we need to run the function `(ΔΓ × ΔA × C2 -> ΔB × C2)` with identity changes on `A` for unchanged parts in a list. To do so, we also need to keep the `Sequence A` part in addition. So, `C` must be `Γ × Sequence (A × C2) × C1`.~~

**Note on Aug 19, 2021** 
Considering the situation that we use the derivative to propagate a part of an update, we need to make sure that we do not duplicate updates unnecessarily. 

A careful treatment is needed for products: `Δ(A × B) ~ ΔA × ΔB`. Consider consecutive updates on `da₁ + da₂` and `db₁ + db₂` on `A` and `B`, respectively. Then, we have `(da₁ + da₂, db₁ + db₂) ~ (da₁, db₁) + (da₂, db₂)`, which might look unsurprising. However, things become difficult when we want to break down an update `da` into atomic ones `da₁ + da₂ + ... + daₙ`, process each `daᵢ` individually, and compose the results to obtain the result for `da`. Then, the treatment of products becomes an issue as it disallows us to process each component separately. For example, if we happen to know `da = da₁ + da₂ + ... + daₙ`, we can decompose the update `(da, db)` into either of 
- `(da₁, db) + (da₂, 0) + ... + (daₙ, 0)` 
- `(da₁, 0) + (da₂, db) + ... + (daₙ, 0) `
- ...
- `(da₁, 0) + (da₂, 0) + ... + (daₙ, db) `
(Here `0` denotes the identity update.) 

The issue would be easy to overlook, when we treat `ΔΓ`. When we implement a function of type `ΔΓ × ΔA × C -> ΔB × C`, we are tempted to consider breaking down an update as `da = da₁ + da₂ + ... + daₙ`. But, it is easy to forget `dγ :: ΔΓ` is processed only once. However, what makes things more confusing is that copying `dγ` itself is valid if the corresponding function `Γ × A -> B` uses `Γ` multiple times. 

Thus, my opinion is that we need to focus on atomic updates `Δ₁A` instead of updates `ΔA`, which we can think is a monoid generated from `Δ₁A`. The monoid `ΔA` must have the following methods
```
lift : Δ₁A -> ΔA
mempty : ΔA 
(<>) : ΔA -> ΔA -> ΔA
hmap : Monoid m => (Δ₁A -> m) -> ΔA -> m  -- monoid homomorphism
```
An easiest solution is to use lists as `ΔA = [Δ₁A]`. Then, we can think a incremetalized morphism as:
```
IF a b = ∃c. (a -> (b, c)) × (Δ₁a -> c -> (Δb × c))
```
Notice that we have `Δ₁(A × B)` is equal to `Δ₁A + Δ₁B`, not `Δ₁A × Δ₁B`. Notice also that `c -> (m, c)` is a monoid if `m` is: 

```
mempty = \c -> (mempty, c) 
f <> g = \c -> 
  let (m1, c1) = f c 
      (m2, c2) = g c1
  in (m1 <> m2, c2) 
```

Thus, we can use `hmap` to convert `(Δ₁a -> c -> (Δb × c))` into `(Δa -> c -> (Δb × c))` so that we can define a composition. 

---

**Note on Aug 19** The new implementation works but the quality of the generated code is poor due to multiple use of continuation code. 

---


## General I/F 

Is there any general I/F for embedding 2nd-order constructs? We could give 

```
semMap :: SemTerm (a : env) b -> SemTerm env (Sequence a) -> SemTerm env (Sequence b)
```

and individually lift such primitives. However, this is quite different from the case of `lift`, `pair` and `unit`, 

     lift :: Sem a b -> e a -> e b 
     pair :: e a -> e b -> e (a, b) 
     unit :: e () 

which are able to lift arbitrary 1st order constructs---i.e., constructs without binders---only by them. We believe, in many cases, they exist as `pair` and `unit` are required to handle a construct with multiple direct subexpressions; e.g., for a construct 

     Γ |- e1 : A1
     Γ |- e2 : A2
     op : A1 × A2 -> A 
     -------------
     Γ |- op e1 e2 : A

a compositional interpretation would be: 

    ⟦ Γ |- op e1 e2 : A ⟧ =
       ⟦ op ⟧ . ⟦ Γ |- e1 : A1 ⟧ `mult` ⟦ Γ |- e2 : A2 ⟧

In this case, the meaning of `op` is determined without refering Γ

Then, what happens for the second-order language constructs? 

     
     { Γ, ~xi:~Ai |- ei : Bi }i 
     op : (~A1 ~> B1), ..., (~An ~> Bn) -> B
     -------------------------------------------
     Γ |- op (~x1.e1) ... (~xn.en) 

    (~x means a sequence x1 ... xm)

I (kztk) am not sure what is actually semantics of `op` in the modern theory of second-order abstract syntax, but it seems to me that they is some relationship between the unembedding and SOAS. 

Anyway, it seems to me that `op` should have the following semantics. 

     ⟦ op ⟧ : forall p. SemTerm (~A1 ++ p) B -> ... -> SemTerm (~A2 ++ p) B -> SemTerm p B 

Can we provide a general extender for this? 

## Function Objects


Is it possible to have an internal hom object in the category? We do not think so. This is due to the abstract nature of `C`. If `C` is concrete, we have 

    (Γ × A -> B × C) × (ΔΓ × ΔA × C -> ΔB × C)
    ~ (Γ -> [A, B] × C') × (ΔΓ × C' -> Δ[A, B] × C')

by taking `C' = 1`, `[A,B] = A -> Writer C B`, and `Δ[A,B] = ΔA -> State C ΔB`; what is important here is that `[A,B]` and `Δ[A,B]` uses the same `C`. 

----
**Note on Aug. 20** Rethinking the problem again, it seems to me that we can take `C'` as `B -> C`, `[A,B] = A -> B` (as standard) and `Δ[A,B] = A -> ΔB` would work.


```
--    (Γ × A -> B × C) × (ΔΓ × ΔA × C -> ΔB × C)
--    ---------------------------------------------------------------------conv
--    (Γ -> (A -> B) × (A -> C)) × (ΔΓ × (A -> C) -> (A -> ΔB) × (A -> C)))
conv (f, tr) = (f', tr') 
  where 
   f' env = (\a -> fst (f (env, a)), \a -> snd (f (env, a)))
   tr' (denv, c) = (\a -> fst (tr (denv, 0, c a)),
                    \a -> snd (tr (denv, 0, c a)))

--    (Γ -> (A -> B) × C) × (ΔΓ × C -> (A -> ΔB) × C)
--    -------------------------------------------------------unconv
--    (Γ × A -> B × C × A) × (ΔΓ × ΔA × C × A -> ΔB × C × A)
unconv (f, tr) = (f', tr') 
  where
    f' (env, a) = let (h, c) = f env in (h a, c, a) 
    tr' (denv, da, c, a) = 
       let (h, c') = tr (denv, c) 
           a' = a + da 
           db = h a' 
        in (db, c', a') 
```

(I have not checked they are roundtripping assumeing some properties on `f` and `tr`. We may also need to use the parametricity for existential types.)


However, this approach essentially prevents the function object to be incremental. This behavior, while unwelcome, would make sense, because where the function `A -> B` is applied depends on `Γ` and thus we cannot know beforehand how to construct the connection between `Γ × A` and `B`. 

----

In the original calculus, `C = Γ × A` and the second component of the initializer is redundant as it just copies the input. In this situation, the equation becomes

    (Γ × A -> B) × (ΔΓ × ΔA × Γ × A -> ΔB)
    ~ (Γ -> [A, B]) × (ΔΓ × Γ -> Δ[A, B])

and solved straightforwardly by taking `[A,B] = A -> B` and `Δ[A,B] = A -> ΔA -> ΔB`.


Anyway, we are able to use the host language's higher-order functions, which essentially interprets the host system in presheaf (in an enriched category). 