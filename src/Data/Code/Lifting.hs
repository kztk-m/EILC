{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
module Data.Code.Lifting where

import           Data.Code
import           Data.Conn
import           Data.Delta            (Delta, Diff, DiffTypeable)
import           Data.Env
import           Data.Functor.Identity
import           Data.Kind             (Type)
import           Data.Typeable         (Typeable)
import           Language.Unembedding  (Wit (Wit))



unCNE :: Conn f ('NE cs) -> NEConn f cs
unCNE (CNE cs) = cs

unCOne :: NEConn f ('NEOne c) -> f c
unCOne (COne c) = c

unCJoin :: NEConn f ('NEJoin c1 c2) -> (NEConn f c1, NEConn f c2)
unCJoin (CJoin c1 c2) = (c1, c2)

conn2code :: Conn PackedCode cs -> Code (Conn Identity cs)
conn2code CNone   = [|| CNone ||]
conn2code (CNE c) = [|| CNE $$(conn2code' c) ||]

conn2code' :: NEConn PackedCode cs -> Code (NEConn Identity cs)
conn2code' (COne (PackedCode c)) = [|| COne (Identity $$c) ||]
conn2code' (CJoin c1 c2)         = [|| CJoin $$(conn2code' c1) $$(conn2code' c2) ||]


code2conn :: forall cs r proxy. Conn proxy cs -> Code (Conn Identity cs) -> (Conn PackedCode cs -> Code r) -> Code r
code2conn CNone      c k = [|| let _ = $$c in $$(k CNone) ||]
code2conn (CNE pcne) c k = code2conn' pcne [|| unCNE $$c ||] (k . CNE)

code2conn' :: forall cs' r proxy. NEConn proxy cs' -> Code (NEConn Identity cs') -> (NEConn PackedCode cs' -> Code r) -> Code r
code2conn' (COne _) c k = k (COne $ PackedCode [|| runIdentity (unCOne $$c) ||])
code2conn' (CJoin pc1 pc2) c k =
  [|| let (c1, c2) = unCJoin $$c
      in $$(code2conn' pc1 [|| c1 ||] $ \c1' -> code2conn' pc2 [|| c2 ||] $ \c2' -> k (CJoin c1' c2')) ||]

type family Func (cs :: Tree Type) (a :: Type) :: Type where
  Func 'None a    = a
  Func ('NE ne) a = Func' ne a

type family Func' (cs :: NETree Type) (a :: Type ) :: Type where
  Func' ('NEOne c) a      = c -> a
  Func' ('NEJoin c1 c2) a = Func' c1 (Func' c2 a)


mkAbs :: forall cs a proxy. Conn proxy cs -> (Conn PackedCode cs -> Code a) -> Code (Func cs a)
mkAbs CNone k    = k CNone
mkAbs (CNE cs) k = mkAbs' cs (k . CNE)

mkAbs' :: NEConn proxy cs -> (NEConn PackedCode cs -> Code a) -> Code (Func' cs a)
mkAbs' (COne _) k      = [|| \a -> $$(k (COne $ PackedCode [|| a ||])) ||]
mkAbs' (CJoin c1 c2) k = mkAbs' c1 $ \c1' -> mkAbs' c2 $ \c2' -> k (CJoin c1' c2')

mkAbsBang :: forall cs a proxy. Conn proxy cs -> (Conn PackedCode cs -> Code a) -> Code (Func cs a)
mkAbsBang CNone k    = k CNone
mkAbsBang (CNE cs) k = mkAbsBang' cs (k . CNE)

mkAbsBang' :: NEConn proxy cs -> (NEConn PackedCode cs -> Code a) -> Code (Func' cs a)
mkAbsBang' (COne _) k      = [|| \ !a -> $$(k (COne $ PackedCode [|| a ||])) ||]
mkAbsBang' (CJoin c1 c2) k = mkAbsBang' c1 $ \c1' -> mkAbsBang' c2 $ \c2' -> k (CJoin c1' c2')


mkApp :: forall cs a. Code (Func cs a) -> Conn PackedCode cs -> Code a
mkApp f CNone    = f
mkApp f (CNE cs) = mkApp' f cs

mkApp' :: Code (Func' cs a) -> NEConn PackedCode cs -> Code a
mkApp' f (COne (PackedCode a)) = [|| $$f $$a ||]
mkApp' f (CJoin c1 c2)         = mkApp' (mkApp' f c1) c2

type family Flatten cs where
  Flatten 'None   = '[]
  Flatten ('NE x) = Flatten' x '[]

type family Flatten' cs r where
  Flatten' ('NEOne c) r = c ': r
  Flatten' ('NEJoin cs1 cs2) r = Flatten' cs1 (Flatten' cs2 r)

enilOfIdentity :: Env Identity '[]
enilOfIdentity = ENil
{-# INLINE enilOfIdentity #-}

conn2cenv :: Conn PackedCode cs -> Code (Env Identity (Flatten cs))
conn2cenv CNone    = [|| enilOfIdentity ||]
conn2cenv (CNE cs) = conn2cenv' cs [|| enilOfIdentity ||]

conn2cenv' :: NEConn PackedCode cs -> Code (Env Identity rs) -> Code (Env Identity (Flatten' cs rs))
conn2cenv' (COne (PackedCode c)) r = [|| ECons (Identity $$c) $$r ||]
conn2cenv' (CJoin c1 c2) r         = conn2cenv' c1 (conn2cenv' c2 r)

seqENil :: Env f '[] -> a -> a
seqENil ENil a = a

cenv2conn :: forall cs r proxy. Conn proxy cs -> Code (Env Identity (Flatten cs)) -> (Conn PackedCode cs -> Code r) -> Code r
cenv2conn CNone  env k = [|| $$env `seqENil` $$(k CNone) ||]
cenv2conn (CNE (p :: NEConn proxy cs')) env k = cenv2conn' @cs' @'[] @r p env $ \c env' ->
  [|| $$env' `seqENil` $$(k (CNE c)) ||]
  -- [|| case $$env' of { ENil -> $$(k (CNE c)) } ||]

cenv2conn' :: forall cs ds r proxy. NEConn proxy cs -> Code (Env Identity (Flatten' cs ds)) -> (NEConn PackedCode cs -> Code (Env Identity ds) -> Code r) -> Code r
cenv2conn' (COne _) env k =
  [||
    let (x, xs) = headTailEnv $$env
    in $$( k (COne (PackedCode [|| runIdentity x ||])) [|| xs ||] )
  ||]
cenv2conn' (CJoin p1 p2) env k =
  cenv2conn' p1 env $ \c1 env' -> cenv2conn' p2 env' $ \c2 env'' -> k (CJoin c1 c2) env''


type family UnFlatten cs = c | c -> cs where
  UnFlatten '[]       = 'None
  UnFlatten (x ': xs) = 'NE (UnFlatten' x xs)

type family UnFlatten' c cs = r | r -> c cs where
  UnFlatten' x '[]      = 'NEOne x
  UnFlatten' x (y : ys) = 'NEJoin ('NEOne x) (UnFlatten' y ys)

convertEnv :: Env f env -> Conn f (UnFlatten env)
convertEnv ENil         = CNone
convertEnv (ECons a as) = CNE $ convertEnv' a as

convertEnv' :: f a -> Env f as -> NEConn f (UnFlatten' a as)
convertEnv' x ENil         = COne x
convertEnv' x (ECons y ys) = CJoin (COne x) (convertEnv' y ys)

unconvertEnv :: Env proxy env -> Conn f (UnFlatten env) -> Env f env
unconvertEnv ENil CNone = ENil
unconvertEnv (ECons _ ps) (CNE x) =
  let (y, ys) = unconvertEnv' ps x
  in ECons y ys

unconvertEnv' :: Env proxy env -> NEConn f (UnFlatten' a env) -> (f a, Env f env)
unconvertEnv' ENil (COne x) = (x, ENil)
unconvertEnv' (ECons _ ps) (CJoin (COne x) xs) =
  let (y, ys) = unconvertEnv' ps xs
  in (x, ECons y ys)

packEnv :: Env PackedCode s -> Code (Env Identity s)
packEnv ENil                      = [|| ENil ||]
packEnv (ECons (PackedCode a) as) = [|| ECons (Identity $$a) $$(packEnv as) ||]

unpackEnv :: Env proxy s -> Code (Env Identity s) -> (Env PackedCode s -> Code r) -> Code r
unpackEnv ENil c k =
  [|| case $$c of { ENil -> $$(k ENil) } ||]
unpackEnv (ECons _ s) c k =
  [|| let (Identity _a, as) = headTailEnv $$c
      in $$(unpackEnv s [|| as ||] (k . ECons (PackedCode [|| _a ||]))) ||]

data WitTypeable a where
  WitTypeable :: Typeable a => WitTypeable a

witTypeableFlatten :: Conn WitTypeable cs -> Wit (Typeable (Flatten cs))
witTypeableFlatten CNone = Wit
witTypeableFlatten (CNE cs) = case witTypeable' cs (Wit :: Wit (Typeable '[])) of { Wit -> Wit }

witTypeable' :: NEConn WitTypeable cs -> Wit (Typeable r) -> Wit (Typeable (Flatten' cs r))
witTypeable' (COne WitTypeable) Wit = Wit
witTypeable' (CJoin c1 c2) wit      = witTypeable' c1 (witTypeable' c2 wit)

witTypeableConn :: Conn WitTypeable cs -> Wit (Typeable (Flatten cs), Typeable cs)
witTypeableConn CNone = Wit
witTypeableConn (CNE cs) = case witTypeableConn' cs (Wit :: Wit (Typeable '[])) of Wit -> Wit

witTypeableConn' :: forall cs r. NEConn WitTypeable cs -> Wit (Typeable r) -> Wit (Typeable (Flatten' cs r), Typeable cs)
witTypeableConn' (COne WitTypeable) Wit = Wit
witTypeableConn' (CJoin (c1 :: NEConn WitTypeable as) (c2 :: NEConn WitTypeable bs)) wit = case witTypeableConn' c2 wit of
   Wit -> case witTypeableConn' c1 (Wit @(Typeable (Flatten' bs r))) of
     Wit -> Wit


type family EFunc as r where
  EFunc '[] r       = r
  EFunc (a ': as) r = a -> EFunc as r

mkAbsE :: forall as r proxy. Env proxy as -> (Env PackedCode as -> Code r) -> Code (EFunc as r)
mkAbsE ENil f         = f ENil
mkAbsE (ECons _ sh) f = [|| \a -> $$(mkAbsE sh (f Prelude.. ECons (PackedCode [|| a ||])) ) ||]

mkAbsED :: forall as r proxy. AllIn as DiffTypeable => Env proxy as -> (Env PackedCodeDiff as -> Code r) -> Code (EFunc as r)
mkAbsED ENil f         = f ENil
mkAbsED (ECons _ sh) f = [|| \a -> $$(mkAbsED sh (f Prelude.. ECons (PackedCodeDiff [|| a ||])) ) ||]

mkAppE :: forall as r. Code (EFunc as r) -> Env PackedCode as -> Code r
mkAppE f ENil                      = f
mkAppE f (ECons (PackedCode a) as) = mkAppE [|| $$f $$a ||] as


mkAppED :: forall as r. Code (EFunc as r) -> Env PackedCodeDiff as -> Code r
mkAppED f ENil                          = f
mkAppED f (ECons (PackedCodeDiff a) as) = mkAppED [|| $$f $$a ||] as


type family DFunc as r where
  DFunc '[] r       = r
  DFunc (a ': as) r = Delta a -> DFunc as r

mkAbsD :: forall as r proxy. (AllIn as DiffTypeable) => Env proxy as -> (Env PackedCodeDelta as -> Code r) -> Code (DFunc as r)
mkAbsD ENil f         = f ENil
mkAbsD (ECons _ sh) f =
  [|| \a -> $$(mkAbsD sh (f Prelude.. ECons (PackedCodeDelta [|| a ||])) ) ||]

mkAppD :: forall as r. Code (DFunc as r) -> Env PackedCodeDelta as -> Code r
mkAppD f ENil                           = f
mkAppD f (ECons (PackedCodeDelta a) as) = mkAppD [|| $$f $$a ||] as
