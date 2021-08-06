{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
module Language.Unembedding (

  HasProduct(..), Term(..),

  App(..),
  Sig2, type (~>),

  CategoryK(..), Wit(..),
  Cartesian(..), TermFromCat(..),
  Fun(..), TermF(..),

  PackTermF(..), PackFun(..), PackFunArg(..), ToEnvProxy(..),
  liftSO0, liftSO1, liftSO2, liftSO3,

  App2(..), TSem,

  run, runMono,
  ) where

-- import           Control.Category
-- import           Control.Category
import           Data.Kind     (Constraint, Type)
import           Prelude       hiding (id, (.))

import           Data.Env
import           Data.Proxy    (Proxy (..))
import           Debug.Trace
import           Text.Printf
import qualified Unsafe.Coerce as Unsafe


class CategoryK (cat :: k -> k -> Type) where
  type K cat :: k -> Constraint
  type K cat = NoConstraint
  id :: K cat a => cat a a
  (.) :: (K cat a, K cat b, K cat c) => cat b c -> cat a b -> cat a c

-- no constraint
class NoConstraint a
instance NoConstraint a

instance CategoryK (->) where
  type K (->) = NoConstraint
  id x = x
  f . g = \x -> f (g x)


data Wit c where
  Wit :: c => Wit c

class CategoryK cat => HasProduct (cat :: k -> k -> Type) where
  type Unit cat :: k
  type Prod cat (a :: k) (b :: k) :: k

  unitOk :: Proxy cat -> Wit (K cat (Unit cat))
  prodOk :: Proxy cat -> Proxy a -> Proxy b -> (K cat a, K cat b) => Wit (K cat (Prod cat a b))


class HasProduct cat => App cat e | e -> cat where
  lift :: (K cat a, K cat b) => cat a b -> e a -> e b
  unit :: (K cat (Unit cat)) => e (Unit cat)
  pair :: (K cat a, K cat b, K cat (Prod cat a b)) => e a -> e b -> e (Prod cat a b)

-- | Fun e ('[t1,...,tn] ~> t) ~ (e t1, ... ,e tn) -> e t
data Fun c (e :: k -> Type) (s :: Sig2 k) :: Type  where
  Fun :: AllIn ts c => Env Proxy ts -> (Env e ts -> e r) -> Fun c e (ts ~> r)

data TermF c term env (s :: Sig2 k) :: Type where
  TermF :: AllIn ts c => term (Append ts env) r -> TermF c term env (ts ~> r)

class App cat e => App2 (cat :: k -> k -> Type) (term :: [k] -> k -> Type) (e :: k -> Type) | e -> term where
  liftSO :: (forall p. Env (TermF (K cat) term p) ss -> term p r) -> Env (Fun (K cat) e) ss -> e r

class ToEnvProxy as where
  toEnvProxy :: Env Proxy as

instance ToEnvProxy '[] where
  toEnvProxy = ENil

instance ToEnvProxy as => ToEnvProxy (a ': as) where
  toEnvProxy = ECons Proxy toEnvProxy


class ToEnvProxy as => PackFunArg c e as a res | e as a -> res, res -> e, res -> a where
  unpackFunArg :: Fun c e (as ~> a) -> res
  packFunArg   :: AllIn as c => res -> Fun c e (as ~> a)

instance res ~ e b => PackFunArg c e '[] b res where
  unpackFunArg (Fun _ f) = f ENil
  packFunArg res = Fun ENil (\ENil -> res)

instance PackFunArg c e as b res => PackFunArg c e (a ': as) b (e a -> res) where
  unpackFunArg (Fun (ECons _ tenv) f) = \arg -> unpackFunArg @c $ Fun tenv (\args -> f $ ECons arg args)
  packFunArg f = Fun toEnvProxy $ \(ECons arg args) ->
    case packFunArg @c @e @as (f arg) of
      Fun _ res -> res args

class PackFun c e ss r res | e ss r -> res, res -> e, res -> r where
  unpackFun :: (Env (Fun c e) ss -> e r) -> res
  packFun   :: res -> (Env (Fun c e) ss -> e r)

instance res ~ e r => PackFun c e '[] r res where
  unpackFun f = f ENil
  packFun f ENil = f

instance (s ~ (as ~> a), PackFunArg c e as a arg, AllIn as c,  PackFun c e ss r res) => PackFun c e (s ': ss) r (arg -> res) where
  unpackFun f = \arg -> unpackFun $ \args -> f (ECons (packFunArg arg) args)
  packFun f (ECons a as) = packFun (f $ unpackFunArg a) as

data Nat = Z | S Nat

type family Length (xs :: [k]) :: Nat where
  Length '[] = 'Z
  Length (a ': as) = 'S (Length as)

class PackTermF c term p ss r res | term p ss r -> res, res -> term, res -> p, res -> r  where
  unpackTermF :: (Env (TermF c term p) ss -> term p r) -> res
  packTermF   :: res -> (Env (TermF c term p) ss -> term p r)

-- instance PackTermF' term p ss (Length ss) r res => PackTermF term p ss r res where
--   unpackTermF = unpackTermF'
--   packTermF = packTermF'

-- class PackTermF' term p ss n r res | term p ss r -> res, res -> term, res -> p, res -> r, res -> n, ss -> n where
--   unpackTermF' :: (Env (TermF term p) ss -> term p r) -> res
--   packTermF'   :: res -> (Env (TermF term p) ss -> term p r)

-- instance PackTermF' term p '[] 'Z r (term p r) where
--   unpackTermF' f = f ENil
--   packTermF' x ENil = x

-- instance (asp ~ Append as p, s ~ (as ~> a),  PackTermF' term p ss n r res) => PackTermF' term p (s ': ss) ('S n) r (term asp a -> res) where
--   unpackTermF' f = \t -> unpackTermF' $ \xs -> f (ECons (TermF t) xs)
--   packTermF' h (ECons (TermF t) xs) = packTermF' (h t) xs

instance PackTermF c term p '[] r (term p r) where
  unpackTermF f = f ENil
  packTermF x ENil = x

instance (asp ~ Append as p, AllIn as c, s ~ (as ~> a), PackTermF c term p ss r res) => PackTermF c term p (s ': ss) r (term asp a -> res) where
  unpackTermF f = \t -> unpackTermF $ \xs -> f (ECons (TermF t) xs)
  packTermF h (ECons (TermF t) xs) = packTermF (h t) xs


-- | These packing functions are not that useful as we need to know the shape of `ss` to perform the conversion.
-- So, we provide some specialized functions. Due to the power of type classes we use, we need to specify binder's types.
--
-- For example, suppose we have @letTm :: Tm s a -> Tm (a : s) b -> Tm s b@ and an instance of @Term C Tm@ for some @C@ and @Tm@.
--
-- Then, we can have a lifted construct as below:
-- @
-- share :: forall e a r. App2 C Tm e => e a -> (e a -> e r) -> e r
-- share = liftSO2 (Proxy '[ '[], '[a] ]) letTm
-- @
--
-- FIXME: It is ugly to use Proxy, but I do not like AllowAmbiguousTypes
-- FIXME: Use TH to generate liftSO4, liftSO5, ...

liftSO0 ::
  forall cat term e r.
  App2 cat term e
  => (forall p. term p r) -> e r
liftSO0 e = unpackFun @(K cat) @e @'[] (liftSO (packTermF e))


liftSO1 ::
  forall cat term e as a arg r.
  (App2 cat term e, PackFunArg (K cat) e as a arg, AllIn as (K cat) )
  => Proxy '[as] -> (forall p. term (Append as p) a -> term p r) -> arg -> e r
liftSO1 _ e = unpackFun @(K cat) @e @'[as ~> a] (liftSO (packTermF e))

liftSO2 ::
  forall cat term e as1 a1 as2 a2 arg1 arg2 r.
  (App2 cat term e, PackFunArg (K cat) e as1 a1 arg1, PackFunArg (K cat) e as2 a2 arg2, AllIn as1 (K cat), AllIn as2 (K cat))
  => Proxy '[as1, as2]
  -> (forall p. term (Append as1 p) a1 -> term (Append as2 p) a2 -> term p r) -> arg1 -> arg2 -> e r
liftSO2 _ e = unpackFun @(K cat) @e @'[as1 ~> a1, as2 ~> a2] (liftSO (packTermF e))

liftSO3 ::
  forall cat term e as1 a1 as2 a2 as3 a3 arg1 arg2 arg3 r.
  (App2 cat term e, PackFunArg (K cat) e as1 a1 arg1, PackFunArg (K cat) e as2 a2 arg2, PackFunArg (K cat) e as3 a3 arg3, AllIn as1 (K cat), AllIn as2 (K cat), AllIn as3 (K cat))
  => Proxy '[as1, as2, as3]
  -> (forall p. term (Append as1 p) a1 -> term (Append as2 p) a2 -> term (Append as3 p) a3 -> term p r) -> arg1 -> arg2 -> arg3 -> e r
liftSO3 _ e = unpackFun @(K cat) @e @'[as1 ~> a1, as2 ~> a2, as3 ~> a3] (liftSO (packTermF e))


-- liftSOp ::
--   forall cat term e p ss r rinput routput.
--   (App2 cat term e, PackTermF term p ss r rinput, PackFun e ss r routput) => Env Proxy ss -> rinput -> routput
-- liftSOp _ e = unpackFun @e @ss (liftSO (packTermF @term @p @ss e))


data Sig2 k = [k] :~> k
type ts ~> t = ts ':~> t

class (CategoryK cat, HasProduct cat) => Term cat (term :: [k] -> k -> Type) | term -> cat where
  -- prop> mapTerm (f . g) = mapTerm f . mapTerm g
  mapTerm  :: (K cat a, K cat b, AllIn s (K cat)) => cat a b -> term s a -> term s b

  multTerm :: (K cat a, K cat b, AllIn s (K cat), K cat (Prod cat a b)) => term s a -> term s b -> term s (Prod cat a b)
  unitTerm :: (AllIn s (K cat), K cat (Unit cat)) => Env Proxy s -> term s (Unit cat)

  var0Term   :: (AllIn s (K cat), K cat a) => Env Proxy s -> term (a ': s) a
  weakenTerm :: (AllIn s (K cat), K cat b, K cat a) =>term s a -> term (b ': s) a

--  letTerm    :: term s a -> term (a ': s) b -> term s b
  unliftTerm :: (K cat a, K cat b) => term '[a] b -> cat a b

type family Products cat (ks :: [k]) :: k where
  Products cat '[]       = Unit cat
  Products cat (k ': ks) = Prod cat k (Products cat ks)

newtype TermFromCat cat as a = TermFromCat (cat (Products cat as) a)

class (CategoryK cat, HasProduct cat) => Cartesian cat where
  multS :: (K cat s, K cat a, K cat b) => cat s a -> cat s b -> cat s (Prod cat a b)
  unitS :: (K cat s, K cat (Unit cat)) => cat s (Unit cat)

  fstS  :: forall a b. (K cat a, K cat b, K cat (Prod cat a b)) => Proxy a -> Proxy b -> cat (Prod cat a b) a
  sndS  :: forall a b. (K cat a, K cat b, K cat (Prod cat a b)) => Proxy a -> Proxy b -> cat (Prod cat a b) b

-- instance (CategoryK cat, Cartesian cat, HasProduct cat) => Term cat (TermFromCat cat) where
--   mapTerm f (TermFromCat x) = TermFromCat (f . x)

--   multTerm (TermFromCat x) (TermFromCat y) = TermFromCat (multS x y)
--   unitTerm _ = TermFromCat unitS

--   var0Term :: forall s a. Env Proxy s -> TermFromCat cat (a ': s) a
--   var0Term _ = TermFromCat @cat @(a ': s) @a (fstS @cat @a @(Products cat s) Proxy Proxy)

--   weakenTerm :: forall s a b. TermFromCat cat s a -> TermFromCat cat (b ': s) a
--   weakenTerm (TermFromCat x) = TermFromCat @cat @(b : s) @a $
--     x . sndS @cat @b @(Products cat s) Proxy Proxy


--   unliftTerm (TermFromCat x) = x . multS id unitS

newtype TSem cat term b = TSem { runTSem :: forall as. AllIn as (K cat) => Env Proxy as -> term as b }

instance Term cat term => App cat (TSem cat term) where
  lift x (TSem e) = TSem $ \tenv -> mapTerm x (e tenv)

  unit = TSem unitTerm
  pair (TSem e1) (TSem e2) = TSem $ \tenv -> multTerm (e1 tenv) (e2 tenv)

  -- share (TSem e0) k = TSem $ \tenv ->
  --   let tenva = ECons Proxy tenv
  --       arg = TSem $ \tenv' -> diffT tenva tenv' var0Term
  --   in letTerm (e0 tenv) (runTSem (k arg) tenva)

allAppend :: (AllIn as c, AllIn bs c) => Proxy c -> Proxy bs -> Env Proxy as -> Wit (AllIn (Append as bs) c)
allAppend _ _ ENil = Wit
allAppend pc pbs (ECons _ xs) =
  case allAppend pc pbs xs of
    Wit -> Wit

instance Term cat term => App2 cat term (TSem cat term) where
  liftSO comb ks = TSem $ \tenv -> comb (mapEnv (convert tenv) ks)
    where
      convert :: forall as a. AllIn as (K cat) => Env Proxy as -> Fun (K cat) (TSem cat term) a -> TermF (K cat) term as a
      convert tenv (Fun etenv f) = case allAppend (Proxy @(K cat)) (Proxy @as) etenv of
        Wit -> TermF $ runTSem (f $ makeArgs Proxy Proxy extendedTEnv extendedTEnv (\x -> x) etenv) extendedTEnv
        where
          -- essentially makes
          --   [trans x0, trans x1, trans x2, ..., trans xn]
          -- where xi refers ith de Bruin index, and trans e = TSem $ \tenv' -> diffT extended tenv' e
          makeArgs :: forall ets ts.
                      (AllIn (Append ts as) (K cat), AllIn as (K cat), AllIn ets (K cat))
                      => Proxy ets -> Proxy as
                      -> Env Proxy (Append ts as)
                      -> Env Proxy ets
                      -> (forall b. K cat b => term (Append ts as) b -> term ets b)
                      -> Env Proxy ts -> Env (TSem cat term) ts
          makeArgs _ _ _ _ _ ENil = ENil
          makeArgs pHs (pAs :: Proxy as) (ECons _ baseEnv) extended weaken (ECons (_ :: Proxy b) (argTypes :: Env Proxy argTys)) =
            let arg :: TSem cat term b
                arg = TSem $ \tenv' -> diffT extended tenv' (weaken $ var0Term baseEnv)
            in ECons arg $ makeArgs pHs pAs baseEnv extended (\x -> weaken (weakenTerm x))  argTypes

          extendedTEnv = appendEnv etenv tenv


--      convert tenv f = TermF (convert' tenv f)

      -- convert' :: Env Proxy as -> Fun (TSem term) (ts ~> r) -> term (Append ts as) r
      -- convert' tenv (Body body) = _
      -- convert' tenv (Abs f)     = _

diffT :: (Term cat term, AllIn as (K cat), AllIn bs (K cat), K cat a) => Env Proxy as -> Env Proxy bs -> term as a -> term bs a
diffT tenv1 tenv2 | trace (printf "Diff: #tenv1 = %d and #tenv2 = %d" (lenEnv tenv1) (lenEnv tenv2)) False = undefined
diffT tenv1 tenv2 =
  diff' (lenEnv tenv2 - lenEnv tenv1) tenv1 tenv2
  where
    diff' :: (Term cat term, AllIn xs (K cat), AllIn ys (K cat), K cat a) => Int -> Env Proxy xs -> Env Proxy ys -> term xs a -> term ys a
    diff' 0 _ _ x             = Unsafe.unsafeCoerce x
    diff' n γ1 (ECons _ γ2) x = weakenTerm $ diff' (n-1) γ1 γ2 x
    diff' _ _ _ _             = error "Unreachable"

runMono :: (Term cat term, K cat a, K cat b) => (TSem cat term a -> TSem cat term b) -> cat a b
runMono f = unliftTerm $ runTSem (f $ TSem $ \tenv -> diffT tenv1 tenv $ var0Term ENil) tenv1
  where
    tenv1 = ECons Proxy ENil

run :: (Term cat term, K cat a, K cat b) => (forall e. App2 cat term e => e a -> e b) -> cat a b
run = runMono
