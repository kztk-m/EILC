# Semantics of Terms-in-Contexts

We mainly consider the semantics

    ⟦ Γ ⊢ e : A ⟧ : ∃C. (Γ -> A × C) × (ΔΓ × C -> ΔA × C)

but one might think why 

    ⟦ Γ ⊢ e : A ⟧ : Γ -> A × (Interact ΔΓ ΔA) 

doesn't work where `Interact a b ~ a -> (b, Interact a b)`. A reason why we do not use the latter form is code generation: to make a value of `Interact a b`, we need to use a recursive definition in the meta level; their arguments must be representable in the object level. However, the issue comes when we consider compositional definitions for pairs, for which we want to define a value of `Interact ΔΓ (ΔA × ΔB)` from `Interact ΔΓ ΔA` and `Interact ΔΓ (ΔA × ΔB)`. If we do not care code generation, the definition is quite easy: 

```haskell
newtype Interact a b = Interact { interact :: a -> (b, Interact a b) } 

pairInteract :: Interact s a -> Interact s b -> Interact s (a, b) 
pairInteract inta0 intb0 
    let int inta intb = Interact $ \env -> 
            let (a, inta') = interact inta env 
                (b, intb') = interact intb env 
            in ((a, b), int inta' intb') 
    in int inta0 intb0 
```

But, for code generation, we need to represent `Interact ΔΓ ΔA` as an object in the target language. Thus, we should put the whole thing in the `Code` type. 

Notice that is `Interact a b = νX. F X` where `F X = a -> b × X`, we can write it as 

    νX.F X ~ ∃C. C × (C -> F C) ~ ∃C. C × (C -> a -> b × C) ~ ∃C. C × (a × C -> b × C)

Thus, the main difference is where `C` appears. 

In Haskell, where we believe that `νX. F X = μX. F X`, we may be able represent `Interact` as 

    μX.F X ~ forall X. (F X -> X) -> X ~ forall X. ((a -> b × X) -> X) -> X 

Actually, we have a function

```haskell 
buildI :: (forall x. ((a -> (b, x)) -> x) -> x) -> Interact a b 
buildI fld = fld Interact 
                       
foldI :: Interact a b -> forall x. ((a -> (b, x)) -> x) -> x 
foldI i f = f $ \a -> let (b, i') = interact i a in (b, foldI i' f)
```

To avoid confusion of handling the universal quantification, let us prepare the type below: 

```haskell
newtype FoldI a b = FoldI { runFoldI :: forall x. ((a -> (b, x)) -> x) -> x }
```

Then, the unit function is defined as

```haskell
unitFoldI :: FoldI s () 
unitFoldI = FoldI $ \i -> 
    let x = i $ \env -> ((), x) 
    in x 
```

indicating that generating recursive definition is unavoidable. Much worse is the parsing function, which requires us to do one step unfolding. So, advantages using "fold/build" dispear. 

```haskell
pairFoldI :: FoldI s a -> FoldI s b -> FoldI s (a, b) 
pairFoldI fa fb = FoldI $ \i -> 
    let x fa_ fb_ = i $ \env -> 
        let (a, fa_') = interact fa_ env 
            (b, fb_') = interact fb_ env 
        in ( (a, b), x fa_' fb_')
    in x (buildI fa) (buildI fb)     
```

(2021-10-06) Discussions here makes me rethink about the relationship to the following formalism of BX.

```haskell
type BX a b = a -> (b, b -> Maybe a)
```

Here, `b -> Maybe a` is just a monadic function. In the incrementalized computaiton, 

```haskell 
type IF a b = a -> (b, CachedDT a b) 
data CachedDT a b where 
    -- c is existentially qualified below 
    CachedDT :: (Delta a -> c -> (Delta b, c)) -> CachedDT a b   
```

Can we make the construction more straightforward by using the basic operations on `Sem` and `DSem` below, if the whole operation is represented in the semantics. 

```haskell
type IF a b = Sem a (b ⊗ DSem' a b) 
```

For example, we have: 

```haskell
-- unitS :: Sem s I 
-- unitD :: DSem s I
-- unitIL :: Sem a (I ⊗ a) 
-- inj :: DSem a b -> Sem I (DSem' a b) 
unit :: IF s I 
unit = unitS >>> unitIL >>> (id ⊗ inj unitD)  

-- pairS :: Sem s a -> Sem s b -> Sem s (a ⊗ b) 
-- transS :: Sem ((a, b), (c, d)) ((a,c), (b,d))
-- inj2 :: (DSem a b -> DSem c d -> DSem e f) -> Sem (DSem' a b ⊗ DSem' c d) (DSem' e f) 
pair :: IF s a -> IF s b -> IF s (a ⊗ b) 
pair fa fb = pairS fa fb >>> transS >>> (id ⊗ inj2 pairD) 
```

This approach seems to work well for products and "let", but may be difficult for "map". What makes "map" so difficult? Maybe, an interaction between `Sem` and `DSem` worlds. As, the examples "unit", "pair", and "let" they can be handled independently. 

(2021-10-08) But, wait. What about the `IFqTEU` case? In `IFqTEU`, the treatment of "let" is a bit complicated because its delta translator remembers let-introduced variables only when it is required for. Naively, a transformation between `a` and `b` is written as:

```
∃a'. (a' < a) × (a' -> b × (∃a''. ∃c. (a'' < a) × (Δa' × a'' × c -> Δb × a'' × c)))
```

But, the `Δa'` part above prohibits us from factorizing the Δ-translator part as a `DSem a b`. It is true that we can use `Δa` for this part as and extract the Δ-translator as `DSem a b` as: 

```
type DSem a b = ∃a''. ∃c. (a'' < a) × (Δa × a'' × c -> Δb × a'' × c)))
```

But, then we are not able to construct `let_ : DSem s a -> DSem (s, a) b -> DSem s b`, because we do not know how to construct `a` value here. 

**Random Thought:** The map API in the current `Sequence.hs` has type

```haskell
forall s a b. Diff a => IFqTEU s (S a) -> IFqTEU (a ': s) b -> IFqTEU s (S b)
```

but, things become a bit simpler with the following type. 

```haskell
forall s a b. Diff a => IFqTEU (a ': s) b -> IFqTEU (S a ': s) (S b)
```

- [x] Check this to know what causes the complication most. 

----

Why is it difficult to implement the map API? One answer would be the manipulation of the `C` part; since it belongs to the `Sem` world but not in the `Code` world. 

-----

I realized that, the `Sem a (b ⊗ DSem' a b)` style is bad for the map API, as the cache part and the Δ-translator `DSem a b` depend on `a`, making it hard to store in homogeneous datatypes like `Sequence` itself. However, there is a motivation to keep the cache part, as some operations on data are common to both data and cache. 

Thus, we may focus on the treatment of Γ and C.

(2021-10-12) Now I feel that the map API is reasonably complex. 

# Discussions on Higher-Order APIs

A interesting problem comes form Giarrusso et al.'s paper: What happens if APIs contains higher-orderness? 

An illustrative example is:
```haskell
singleton :: a -> Sequence a 
map :: (a -> b) -> Sequence a -> Sequence b 
concat :: Sequence (Sequence a) -> Sequence a
empty :: Sequence a 
```
which is used to define 

```haskell
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
__[This approach is not effective at all. See the comment on Aug 20]__
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

**Note on Aug 19** The new implementation works but the quality of the generated code is poor due to multiple use of continuation code. 

**Note on Aug 20** I should rethink about the approach to consider atomic updates. In a naive approach, we should consider atomic update to environments. But, this approach requires us to copy continue code twice for `let` and `map`, for which we need to propagate updates both on `A` and `Γ` to produce an update on `B`. The index-based approach, in which indices are "static" information to avoid the indexing cost in runtime, requires us to __use__ (not just **run**) the continuation code (that corresponds to a term-in-context `Γ, x : A ⊢ e : B` as the generated code can differ for the index given. The produced code must handle the case where `x` is updated and somewhere in `Γ` is updated, but we cannot handle this case by using the one code obtained from `e` as the generated code for these cases can be different. 

Also, even though we consider atomic updates, what we will obtain is the sequence of updates on the sequence instead of an atomic update, and we have to consider how to combine them with an update on `\Gamma`; the source of the trouble mentioned above is still there. Notice that we cannot assume that an atomic update is produced for an atomic update. The granularity of updates may differ for data. It may be impossible for us to avoid running the code as many as the number of atomic updates, but we are hoping that this can be done by using one code. 


**Aug 26, 2021** The issue of code duplication has been resolved. However, the result is not yet satisfactory. We need to know whether `ΔΓ` affects the delta translator `(ΔΓ × ΔA × C2 -> ΔB × C2)`, as it requires us to map the function to the connections (caches) (`Sequence C2`), which is rather costly. Also, the `map` API requires us to run `f` of `map f` if an insertion happens. To handle the case, the implementation of the API map keep the `Γ` to obtain an updated version of `f`, while we know updating the free variables in `f` (or `f`'s closure is enough). This means O(n) memory is required if `map` is nested `n` times.

**Aug 27, 2021** I implemented a new interface that interprets terms-in-context `Γ |- e : A` as 

    ∃C. (Γ -> A × C) × (Γ × ΔΓ × C -> ΔA × C) 

(Here, the delta translater part takes additional argument Γ.) This approach removes the issue of quadratic memory consumption of `map`.

There is a still some issues in this approach: we need to keep track of `Γ` information, whether or not this is useful or not. For example, for "let"

    (Γ -> A × C₁) × (Γ × ΔΓ × C₁ -> ΔA × C₁) 
    (Γ × A -> B × C₂) × (Γ × A × ΔΓ × ΔA × C₂ -> ΔB × C₂) 
    ------------------------------------------------------(let) 
    ∃C. (Γ -> B × C) × (Γ × ΔΓ × C -> ΔB × C) 

We must include the information of `A` to `C`, e.g., as `C = C₁ × C₂ × A`, in order to call the delta translator associated with the let body. But in many cases, we do not need to do so. FOr example, among the sequence combinators, only `map` requires the `Γ` part. A related observation is that `map`'s delta translator uses the `\Gamma` used in the forward computation, in addition to the `\Gamma` part used in the computation of delta translators. 

**Aug 30, 2021** Implemented the idea above in `./Data/IFqTEU.hs` ("IF", "q", "T", "E" and "U" stand for "incrementalized functions", "quoted", "terms", "environments", and "uses", respectively). We have not tested the 'map' API. Code generation takes at least quadratic time due to handling of free variables. 

**Oct 1, 2021** Let me summarize the idea in `Data.IFqTEU` that interprets `Γ ⊢ e : A` as 

    ∃C. (Γᵤ -> A × C) × (Γᵤ' × ΔΓᵤ × C -> ΔA × C) 

Here, `Γᵤ` is a binding that is sufficient to evaluate `e` (an environment obtained from Γ by removing unused variables in e) and `Γᵤ'` is a subbinding of Γ that is used to run the Δ translator. Why we need to use such argument? 

 - Δ-translator of `map f` uses Γᵤ for insertions to run `f`. 
    - Puting it in `C` when needed is less efficient as it requires to copy Γᵤs for each use. 
 - However, in many cases, Δ-translators do not need Γ.
 - So, it requires Γᵤ' which is expected to be no larger than Γᵤ. 

However, due to handling of them, the implementation of `map` gets so complicated. __Question: Can we give more simpler ways?__ At least for the simpler version, we can make from the original 

```
Δmap : (A -> B) -> (A -> ΔA -> ΔB) -> Seq A -> Δ(Seq A) -> Δ(Seq B) 
```

the 

```
(Γ × A -> B × C₁) × (ΔΓ × ΔA × C₁ -> ΔB × C₁)
(Γ -> Seq A × C₂) × (ΔΓ × C₂ -> Δ(Seq A) × C₂)
-----------------------------------------------(map)
∃C. (Γ -> Seq B × C) × (ΔΓ × C -> Δ(Seq B) × C)
```

but the construction suggests that we need to recompute things when we need to use the associated Δ translator---spoiling the usefulness of the cache transfer style. 

**Oct 20, 2021** I realized that `map f` uses the code of `f` twice: one is in its cache construction and the other is in the Δ translator. This causes code duplication, but currently there is no 
way to share code for cache construction and the Δ-translator except using `C`; but such a transformation itself does not depends on Δs and thus it is not a good idea to store them in `C`. 


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

----

**Oct 22, 2021** A notion called closure change is considered in Giarrusso et al.'s cache-transfer system. The basic idea is to consider a closure 

    ∃Γ. (Γ × A -> B) × Γ 

and changes to it     

    ∃Γ. (Γ × A -> Δ(Γ × A) -> ΔB) × ΔΓ

In the cache-transfer system, as these functions involve cache and are changed accordingly as: 

    ∃Γ. (Γ × A -> B × C) × Γ 
    ∃Γ. (Γ × A -> Δ(Γ × A) -> C -> ΔB × C) × Γ × ΔΓ 

However, there is a severe problem: since Γ is existentially quantified, the delta is actually inapplicable. Their workaround is to include the original function in the second one as

    ∃Γ. (Γ × A -> B × C) × (Γ × A -> Δ(Γ × A) -> C -> ΔB × C) × Γ × ΔΓ  

and define the update application operator ⊕ as: 

    _ ⊕ (f, df, θ, dθ) = (f ⊕ df, θ ⊕ dθ)

Clearly, this approach does not support composition of updates in general. They actually wrote in their code as: 

> ```haskell 
> -- Since this composition function is problematic, do not export it through typeclasses, which allow using it implicitly.
> -- instance CompChangeStruct (Fun a b c) where
> --   ocompose = composeDFun
> ```

Then, let's rethink how we express functions in our system. If we allow ourselves to expose `C`, a straightforward approach is to use `[A, B] = A -> B × C`, `Δ[A, B] = ΔA × C -> ΔB × C`
and `C' = ()` in the below. 

    (Γ × A -> B × C) × (ΔΓ × ΔA × C -> ΔB × C)
    ~ (Γ -> [A, B] × C') × (ΔΓ × C' -> Δ[A, B] × C')

But, `[A, B]` and `Δ[A, B]` clearly cannot expose `C`, as it is not included in the type parameter and hidden by using the existential quantification. So, we use `Dynamic` as below. 

```haskell
data Dynamic where 
  Dynamic :: TypeRep a -> a -> Dynamic 
```

Since the construction of `TypeRep` is only allowed by using the type class method of `Typeable`, one can think the above is 

```haskell 
data Dynamic where 
  Dynamic :: Typeable a => a -> Dynamic 
```

meaning that we can hide the type of a value if its type is an instance of `Typeable`, which guarantees same downcasting. So, our suggestion is to use `Dynamic` instead of `C` to address the issue of the exposure, while we internally treat them as `C` by casting.  

```
 [A, B] = A -> B × Dynamic
Δ[A, B] = ΔA × Dynamic -> ΔB × Dynamic 
```

A caveat here is the behavior of Δ-translator `Δ[A, B]` is a bit different from what is obtained from the interpretation `∃C. (Γ -> A × C) × (ΔΓ × C -> ΔA × C)` of a term-in-context `Γ ⊢ e : A`. The latter is guaranteed to produce nil changes and no changes on its internal state if `ΔΓ` is a nil change. However, there is no such guarantee for the former one, which is intuitively because a function can have free variables and changes to the values of such free variables lead to the change on its result. 

The original paper say an element of `Δ[A, B]` that satisfies the above property a nil function change. As we can define 

    f ⊕ df = \a ->
         let (b,  c1) = f a
             (db, c2) = df 0 c1 
         in (b ⊕ db, c2) 

However, this definition is not enough to determine how the composition of `Δ[A,B]` elements behaves: we cannot determine the ??? part below, which can either be `0` or `da` to make the above equation to hold. 

     df ⊕ df' = \(da, c) -> 
                   let (db1, c1) = df  ??? c  
                       (db2, c2) = df' ??? c1 
                   in (db1 ⊕ db2, c2) 

(We assumed that `f`, `df` and `df'` hold the same `C` internally.) 

In the original paper, a function change is required to satify the following law:

     f a ⊕ df a da = (f ⊕ df) (a ⊕ da) 

This may correspond to the below one in our setting. 

     let (b,  c)  = f a 
         (db, c') = df da c 
     in (b ⊕ db, c') 
     = 
     let (b,  c1)  = f (a ⊕ da)
         (db, c' ) = df 0 c1 
     in (b ⊕ db, c') 

Replacing `df` with `df1 ⊕ df2` yields.

     let (b,  c1) = f a 
         (db1, c2) = df1 ??? c1
         (db2, c3) = df2 ??? c2 
     in (b ⊕ db1 ⊕ db2, c2)
     = 
     let (b,   c1)  = f (a ⊕ da)
         (db1, c' ) = df1 0 c1 
         (db2, c' ) = df2 0 c1 
     in (b ⊕ db1 ⊕ db2, c') 

Then, we use the above equation again for the RHS to obtain: 

     let (b,   c1)  = f (a ⊕ da)
         (db1, c' ) = df1 0 c1 
         (db2, c' ) = df2 0 c1 
     in (b ⊕ db1 ⊕ db2, c') 
     = 
     let (b,   c1)  = f a
         (db1, c' ) = df1 da c1 
         (db2, c' ) = df2 0 c1 
     in (b ⊕ db1 ⊕ db2, c') 
 
This suggest that the composition must satisfy the below. 

     df ⊕ df' = \(da, c) -> 
                   let (db1, c1) = df  da c  
                       (db2, c2) = df' 0  c1 
                   in (db1 ⊕ db2, c2) 

Also, since we have `f ⊕ df ⊕ df' = (f ⊕ df) ⊕ df'`, we have: 

     let (b,   c1)  = (f ⊕ df1) (a ⊕ da)
         (db2, c' ) = df2 0 c1 
     in (b ⊕ db1 ⊕ db2, c') 
    =
     let (b,   c1)  = (f  ⊕ df1) a
         (db2, c' ) = df2 da c1 
     in (b ⊕ db1 ⊕ db2, c') 
     =      
     let (b,   c1)  = f a
         (db1, c2) = df1 0  c1 
         (db2, c') = df2 da c2
     in (b ⊕ db1 ⊕ db2, c') 

- [x] Check this more carefully. 

Thus, the net effect is the same with the definition below: 

     df ⊕ df' = \(da, c) -> 
                   let (db1, c1) = df  0  c  
                       (db2, c2) = df' da c1 
                   in (db1 ⊕ db2, c2) 

Here, `df` satisfying `df 0 c = (0, c)` is called nil change, as it satisfies `f ⊕ df = f`. 

------------------

**2021-11-02** Function objects obtained as above is not that useful, because it does not support separation of updates (`da = da1 ⊕ da2`). I think this is a problem intrinsic to the original calculus so I here use the original formalism for simplicity. 

In the original calculus, `Δ(a -> b) = a -> Δa -> Δb`, but this does not mean that the corresponding delta is a derivative. Instead, in general, what we have is only: 

    (f ⊕ df) (a ⊕ da) = f a ⊕ df a da 

As a special case, we have 

    (f ⊕ df) a = f a ⊕ df a 0 

Hence, `df` is a derivative of `f` only when `df a 0 = 0` and thus `(f ⊕ df) a = f a`. This is roughly because `df` involves an effect of changes to free variables in `f`. 

However, here comes an issue. In practice, we want to define a set `Δa` of updates as a sequence of atomic updates and consider translation of such small updates. This is not possible for `df` as 

    df a (da ⊕ da') 

is not necessarily equal to 

    df a da ⊕ df (a ⊕ da) da' 

as `df` may not be a nil change. Especially, we do not have 

    df a 0 = df a 0 ⊕ df a 0 

for such an `a` that `df a 0 /= 0`. 

Let us consider a concrete example of `map`. Let us assume for simplicity that updates are only compositions of in-place updates such as `At i da`. How can we reflect `[At i da]`? It is not correct if we return `At i (df ai da)` where `ai` is the ith element of the original sequence, because `df` contains the change to `f` itself. So, the correct result actually is the sequence of updates: 

    [At 0 (df a0 0), ..., 
     At (i-1) (df a(i-1) 0), At i (df a 0), At (i+1) (df a(i+1) 0), ...]

This suggests that we losed the compositionality here: the translation results of `[At i da]` and `[At j db]` do not compose to produce the translation result of `[At i da, At j db]`. Fortunately, for this map and this set of updates, we can compute some canonical form of updates and then translate it. But, this is not necessarily possible in general. 

So, in the original calculus, higher-order API is useful only when `df` is an nil update. 

Giarrusso et al.'s addresses the issue by considering closures explicitly. In this context, we can simply view the approach as one that separates `df` into 

   * `dfNN`: a reaction to updates on free variables in `f`.  
   * `df0`: a reaction to updates on `f`'s argument, assuming there are no updates on free variables, which is a derivative of `f`. 

such a way that `df a da = dfNN a ⊕ df0 a da`. 

Now the translation of `[At i da]` is written as 

    [At 0 (dfNN a0), At 1 (dfNN a1), ... ] ++ [At i (df0 ai da)] 

and the translation result of `[At i da, At j db]` is obtained as: 

    [At 0 (dfNN a0), At 1 (dfNN a1), ... ] ++ [At i (df0 ai da), At j (df0 aj db)]

(We assumed `i /= j`. If `i = j`, we should use `(ai ⊕ df0 ai da)` instead of `aj`). 

Looks good? But a pitfall comes when we construct `dfNN` and `df0`. Very roughly speaking, they are obtained as a semantic function to handle 

    Γ , x : A ⊢ e : B 
    ------------------
    Γ ⊢ λx. e : A -> B

that is 

    (h :: Γ × A -> B) × (dh :: Γ × A -> ΔΓ x ΔA -> ΔB) 
    ---------------------------------------------------
    (l :: Γ -> A -> B) × (dl :: Γ -> ΔΓ -> (A -> ΔB) × (A -> ΔA -> ΔB)) 

Here, we have

    dl θ dθ = (\a -> dh (θ, a) (dθ, 0)，\a da -> dh (θ ⊕ dθ, a) (0, da))

Then, how we can construct 0 out of the air? For first-order datatypes, it is usually a part of definition of `Δa`, especially when `Δa` can be decomposed into sequence of atomic updates. However, for functions, we are not able to construct such a term out of the air as they are derivatives.

An observation is that we can "nullify" a function delta as: 

    nullify (_, df) = (const 0, df) 

when the range type is not a function. However, to do so `dfNN` must take a `Δa` to be nullified. If we allow `dfNN` to take `Δa` values that have been nullified, we can avoid the issue of nullification as: 

    -- df is derivative and thus maps empty change to empty change
    nullify (_, df) = (df, df)
    
Then, the application of `dfNN` and `df0` can be defined via: `df a da = dfNN a (nullify da) ⊕ df0 a da`. Here, composition of `(dfNN, df0)` and `(dfNN', df0')` is defined as 

     (\a da0 -> dfNN a da0 ⊕ dfNN' a da0, 
      \a da -> df a da ⊕ df (a ⊕ da) da)

assuming that `da0` is always a null change. **(Really?)**

Function application is defined via 

    -----------------------------------------------------------------------------------
    ((A -> B) × A -> B) × ((A -> B) × A -> (A -> ΔA -> ΔB) × (A -> ΔA -> ΔB) × ΔA -> ΔB)

where the latter part is defined as 

    dapp (f, a) (dfNN, df0, da) = dfNN a (nullify da) ⊕ df0 a da 

- [ ] Check this works for our setting. 


