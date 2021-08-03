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
    ∃C. (Γ × A -> A × C) × (ΔΓ × ΔA × C -> ΔB × C)
    -----------------------------------------------------------
    ∃C. (Γ -> Sequence B × C) × (ΔΓ × C -> Δ(Sequence B) × C) 

The definition fo this API depends on a concrete definition of Δ(Sequence a), but with appropriate definitions of them, we can give one. 

Is it possible to have an internal hom object in the category? We do not think so. This is due to the abstract nature of `C`. If `C` is concrete, we have 

    (Γ × A -> B × C) × (ΔΓ × ΔA × C -> ΔB × C)
    ~ (Γ -> [A, B] × C') × (ΔΓ × C' -> Δ[A, B] × C')

by taking `C' = 1`, `[A,B] = A -> Writer C B`, and `Δ[A,B] = ΔA -> State C ΔB`; what is important here is that `[A,B]` and `Δ[A,B]` uses the same `C`. 

In the original calculus, `C = Γ × A` and the second component of the initializer is redundant as it just copies the input. In this situation, the equation becomes

    (Γ × A -> B) × (ΔΓ × ΔA × Γ × A -> ΔB)
    ~ (Γ -> [A, B]) × (ΔΓ × Γ -> Δ[A, B])

and solved straightforwardly by taking `[A,B] = A -> B` and `Δ[A,B] = A -> ΔA -> ΔB`.


Anyway, we are able to use the host language's higher-order functions, which essentially interprets the host system in presheaf (in an enriched category). 

Also, we can handle 2nd order APIs, which would be useful for the uses cases discussed by Giarrusso et al.'s (**Really?**). 

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
