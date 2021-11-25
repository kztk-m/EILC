{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeOperators             #-}

{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE UndecidableInstances      #-}


module Data.IFqTU where

import           Data.Code            (Code, CodeC (..), PackedCode (..),
                                       PackedCodeDelta (..),
                                       PackedCodeDiff (PackedCodeDiff), mkLet)
import           Data.Conn
import           Data.Delta           (Delta, Diff, pairDelta)
import           Data.Env             (AllIn, Env (..))
import           Data.IFq             (IFqS (..), convTEnv)
import           Data.Proxy           (Proxy)
import           Language.Unembedding (LetTerm (..), Term (..), Wit (Wit))

import           Data.Code.Lifting    (WitTypeable (WitTypeable))
import           Data.JoinList
import           Data.Typeable        (Typeable)
import           Prelude              hiding (id, (.))
import qualified Prelude

data SBool b where
  STrue  :: SBool 'True
  SFalse :: SBool 'False

type family Extr (as :: [k]) (bs :: [Bool]) :: [ k ] where
  Extr _as '[] = '[]
  Extr '[] _us = '[]
  Extr (a ': as) ('True ': us) = a ': Extr as us
  Extr (a ': as) ('False ': us) = Extr as us

--- >>> :k Extr '[ 'Int, 'Double ] '[ 'True, 'True ]
-- Not in scope: data constructor ‘Int’
-- Not in scope: data constructor ‘Double’

type family Or (a :: Bool) (b :: Bool) :: Bool where
  Or 'True _ = 'True
  Or 'False b = b

type family MergeUses (us1 :: [Bool]) (us2 :: [Bool]) :: [Bool] where
  MergeUses '[] bs = bs
  MergeUses (a ': as) '[] = a ': as
  MergeUses (a ': as) (b ': bs) = Or a b ': MergeUses as bs

-- newtype RearrEnv as bs = RearrEnv { rearrEnv :: forall f. Env f as -> Env f bs }
-- data RearrEnvExt us1 us2 =
--   RearrEnvExt { unRearrEnvExt :: forall xs. Proxy xs -> RearrEnv (Extr xs us1) (Extr xs us2) }

extractingByNilIsNil :: forall bs f proxy. Env proxy bs -> Env f (Extr bs '[])
extractingByNilIsNil ENil        = ENil
extractingByNilIsNil (ECons _ _) = ENil


keepElem :: (Env f as -> Env f bs) -> Env f (a ': as) -> Env f (a ': bs)
keepElem f (ECons x xs) = ECons x (f xs)

dropElem :: (Env f as -> Env f bs) -> Env f (a ': as) -> Env f bs
dropElem f (ECons _ xs) = f xs

newtype RearrEnv as us us' =
  RearrEnv { rearrEnv :: forall f. Env f (Extr as us) -> Env f (Extr as us') }


mergeUses :: Env SBool us1 -> Env SBool us2 -> Env SBool (MergeUses us1 us2)
mergeUses ENil us           = us
mergeUses (ECons u us) ENil = ECons u us
mergeUses (ECons u1 us1) (ECons _u2 us2) = case u1 of
  STrue  -> ECons STrue (mergeUses us1 us2)
  SFalse -> ECons _u2   (mergeUses us1 us2)

mergeTupled ::
  forall us1 us2 as proxy.
  Env SBool us1 -> Env SBool us2 -> Env proxy as
  -> (Env SBool (MergeUses us1 us2),
      RearrEnv as (MergeUses us1 us2) us1,
      RearrEnv as (MergeUses us1 us2) us2)
mergeTupled ENil us2 tenv           = (us2, RearrEnv $ const $ extractingByNilIsNil tenv, RearrEnv Prelude.id)
mergeTupled (ECons u1 us1) ENil tenv = (ECons u1 us1, RearrEnv Prelude.id, RearrEnv $ const $ extractingByNilIsNil tenv)
mergeTupled (ECons u1 us1) (ECons u2 us2) ENil = (mergeUses (ECons u1 us1) (ECons u2 us2), RearrEnv Prelude.id, RearrEnv Prelude.id)
mergeTupled (ECons STrue us1) (ECons STrue us2) (ECons _ tenv)
  = let (us, f1, f2) = mergeTupled us1 us2 tenv
    in (ECons STrue us, RearrEnv $ keepElem (rearrEnv f1), RearrEnv $ keepElem (rearrEnv f2))
mergeTupled (ECons STrue us1) (ECons SFalse us2) (ECons _ tenv)
  = let (us, f1, f2) = mergeTupled us1 us2 tenv
    in (ECons STrue us, RearrEnv $ keepElem (rearrEnv f1), RearrEnv $ dropElem (rearrEnv f2))
mergeTupled (ECons SFalse us1) (ECons STrue us2) (ECons _ tenv)
  = let (us, f1, f2) = mergeTupled us1 us2 tenv
    in (ECons STrue us, RearrEnv $ dropElem (rearrEnv f1), RearrEnv $ keepElem (rearrEnv f2))
mergeTupled (ECons SFalse us1) (ECons SFalse us2) (ECons _ tenv)
  = let (us, f1, f2) = mergeTupled us1 us2 tenv
    in (ECons SFalse us, RearrEnv (rearrEnv f1), RearrEnv (rearrEnv f2))



extractEnv :: Env f as -> Env SBool us -> Env f (Extr as us)
extractEnv ENil _                         = ENil
extractEnv (ECons _ _) ENil               = ENil
extractEnv (ECons a as) (ECons STrue us)  = ECons a (extractEnv as us)
extractEnv (ECons _ as) (ECons SFalse us) = extractEnv as us

witExtr :: AllIn as k => Proxy k -> Env proxy as -> Env SBool us -> Wit (AllIn (Extr as us) k)
witExtr _  _            ENil             = Wit
witExtr _  ENil         _                = Wit
witExtr pk (ECons _ as) (ECons STrue us) = case witExtr pk as us of
  Wit -> Wit
witExtr pk (ECons _ as) (ECons SFalse us) = case witExtr pk as us of
  Wit -> Wit

type family CSing (cs :: JoinList k) (as :: [k]) (bs :: [Bool]) :: JoinList k where
  CSing cs '[] _ = cs
  CSing cs (_ ': _) '[] = cs
  CSing cs (a ': _) ('True  ': _) = Join ('JLNonEmpty ('JLSingle a)) cs
  CSing cs (_ ': _) ('False ': _) = cs

type family SafeTail (as :: [k]) :: [k] where
  SafeTail '[] = '[]
  SafeTail (a ': as) = as

safeTail :: Env f as -> Env f (SafeTail as)
safeTail ENil         = ENil
safeTail (ECons _ xs) = xs

extendEnv ::
  Env proxy as -> Env SBool us2
  -> ff a
  -> Env ff (Extr as (SafeTail us2)) -> Env ff (Extr (a : as) us2)
extendEnv _ u2 e env = case u2 of
  ENil           -> ENil
  ECons SFalse _ -> env
  ECons STrue  _ -> ECons e env

--
data IFqTU as b =
  forall cs us.
  IFqTU
      (Env WitTypeable as)
      (Conn WitTypeable cs)
      (Env SBool us)
      (CodeC (Env PackedCodeDiff  (Extr as us) -> CodeC (Code b, Conn PackedCode cs),
              Env PackedCodeDelta (Extr as us) -> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs)))

instance Term IFqS IFqTU where
  mapTerm (IFqS sh2 m2) (IFqTU tenv sh1 u1 m1)
   = IFqTU tenv (joinConn sh1 sh2) u1 $ do
        (f1, tr1) <- m1
        (f2, tr2) <- m2
        let f a = do
              (b, c1) <- f1 a
              (c, c2) <- f2 b
              return (c, joinConn c1 c2)
        let tr da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
              (db, c1') <- tr1 da c1
              (dc, c2') <- tr2 db c2
              return (dc, joinConn c1' c2')
        return (f, tr)


  multTerm (IFqTU tenv sh1 u1 m1) (IFqTU _ sh2 u2 m2)
    = IFqTU tenv (joinConn sh1 sh2) u $ do
        (f1, tr1) <- m1
        (f2, tr2) <- m2
        let
          f s = do
            (a, c1) <- f1 (rearrEnv ext1 s)
            (b, c2) <- f2 (rearrEnv ext2 s)
            r <- mkLet [|| ($$a, $$b) ||]
            return (r , joinConn c1 c2)

          tr ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
            (da, c1') <- tr1 (rearrEnv ext1 ds) c1
            (db, c2') <- tr2 (rearrEnv ext2 ds) c2
            r <- mkLet [|| pairDelta $$da $$db ||]
            return ( r, joinConn c1' c2' )
        return (f, tr)
    where
      (u, ext1, ext2)    = mergeTupled u1 u2 tenv

  unitTerm tenv = IFqTU (convTEnv tenv) CNone ENil $
    return (\_ -> return ([|| () ||], CNone),
            \_ _ -> return ([|| mempty ||], CNone))

  var0Term tenv = IFqTU (ECons WitTypeable $ convTEnv tenv)
                         CNone
                         (ECons STrue ENil) $
                         return (\(ECons (PackedCodeDiff a) _) -> return (a, CNone),
                                 \(ECons (PackedCodeDelta da) _) _ -> return (da, CNone))

  weakenTerm (IFqTU tenv sh u m) = IFqTU (ECons WitTypeable tenv) sh (ECons SFalse u) m

  unliftTerm :: forall a b. (Typeable a, Diff a) =>  IFqTU '[a] b -> IFqS a b
  unliftTerm (IFqTU _ (sh :: Conn WitTypeable cs) (u :: Env SBool us) m) = IFqS sh $ do
    (f, tr) <- m
    let f' a = f (mkEnv u $ PackedCodeDiff a)
        tr' da c = tr (mkEnv u $ PackedCodeDelta da) c
    return (f', tr')

    where
      mkEnv :: forall vs f aa. Env SBool vs -> f aa -> Env f (Extr '[aa] vs)
      mkEnv uu a = case uu of
        ENil           -> ENil
        ECons SFalse _ -> ENil
        ECons STrue  _ -> ECons a ENil



instance LetTerm IFqS IFqTU where
  letTerm :: forall as a b. (Diff a, Typeable a) => IFqTU as a -> IFqTU (a ': as) b -> IFqTU as b
  letTerm (IFqTU tenv (sh1 :: Conn WitTypeable cs1) (u1 :: Env SBool us1) m1)
          (IFqTU _    (sh2 :: Conn WitTypeable cs2) (u2 :: Env SBool us2) m2)
    = IFqTU tenv (joinConn sh1 sh2) uf $ do
      (f1, tr1) <- m1
      (f2, tr2) <- m2
      let f :: Env PackedCodeDiff (Extr as (MergeUses us1 (SafeTail us2)))
              -> CodeC (Code b, Conn PackedCode (Join cs1 cs2))
          f env = do
            (a, c1) <- f1 (rearrEnv ext1 env)
            (b, c2) <- f2 (ext a env)
            let c = joinConn c1 c2
            return (b, c)
            where
              ext :: Code a -> Env PackedCodeDiff (Extr as (MergeUses us1 (SafeTail us2))) -> Env PackedCodeDiff (Extr (a : as) us2)
              ext x = extendEnv tenv u2 (PackedCodeDiff x) Prelude.. rearrEnv ext2
          tr ::
            Env PackedCodeDelta (Extr as (MergeUses us1 (SafeTail us2)))
            -> Conn PackedCode (Join cs1 cs2)
            -> CodeC (Code (Delta b), Conn PackedCode (Join cs1 cs2))
          tr denv cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
            (da, c1') <- tr1 (rearrEnv ext1 denv) c1
            (db, c2') <- tr2 (extd (PackedCodeDelta da) denv) c2
            return (db, joinConn c1' c2')
            where
              extd :: ff a -> Env ff (Extr as (MergeUses us1 (SafeTail us2))) -> Env ff (Extr (a : as) us2)
              extd x = extendEnv tenv u2 x Prelude.. rearrEnv ext2
      return (f, tr)
    where
      uf    :: Env SBool (MergeUses us1 (SafeTail us2))
      ext1 :: RearrEnv as (MergeUses us1 (SafeTail us2)) us1
      ext2 :: RearrEnv as (MergeUses us1 (SafeTail us2)) (SafeTail us2)

      (uf, ext1, ext2) = mergeTupled u1 (safeTail u2) tenv


