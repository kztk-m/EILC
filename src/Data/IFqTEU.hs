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


module Data.IFqTE where

import           Data.Code            (Code, CodeC, PackedCode (..),
                                       PackedCodeDelta (..), mkLet)
import           Data.Delta           (Delta, Diff ((/+)), pairDelta)
import           Data.Env             (Env (..))
import           Data.IFq             (Conn (..), IFq (..), IsNone (..), Join,
                                       NEConn (..), NETree (..), Tree (NE),
                                       decompConn, isNone, joinConn)
import           Data.Proxy           (Proxy (Proxy))
import           Language.Unembedding (LetTerm (..), Term (..))


data SBool b where
  STrue  :: SBool 'True
  SFalse :: SBool 'False

type family Extr (as :: [k]) (bs :: [Bool]) :: [ k ] where
  Extr '[] _us = '[]
  Extr (a ': as) '[] = '[]
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

extractingByNilIsNil :: forall bs f. Env Proxy bs -> Env f (Extr bs '[])
extractingByNilIsNil ENil        = ENil
extractingByNilIsNil (ECons _ _) = ENil


extractFst ::
  forall us1 us2 as f.
  Env SBool us1 -> Env SBool us2 -> Env Proxy as ->
  Env f (Extr as (MergeUses us1 us2)) -> Env f (Extr as us1)
extractFst ENil _ tenv0 = const $ extractingByNilIsNil tenv0
extractFst (ECons _ _) ENil _ = id
extractFst (ECons STrue _) (ECons _ _) ENil = id
extractFst (ECons STrue us1) (ECons _ us2) (ECons _ tenv) = \(ECons x xs) -> ECons x $ extractFst us1 us2 tenv xs
extractFst (ECons SFalse _  ) (ECons STrue _  ) ENil = id
extractFst (ECons SFalse us1) (ECons STrue us2) (ECons _ tenv)
  = \(ECons _ xs) -> extractFst us1 us2 tenv xs
extractFst (ECons SFalse _  ) (ECons SFalse _  ) ENil = id
extractFst (ECons SFalse us1) (ECons SFalse us2) (ECons _ tenv)
  = extractFst us1 us2 tenv

extractSnd  ::
  forall us1 us2 as f.
  Env SBool us1 -> Env SBool us2 -> Env Proxy as ->
  Env f (Extr as (MergeUses us1 us2)) -> Env f (Extr as us2)
extractSnd ENil _us2 _tenv                    = id
extractSnd (ECons _u1 _us1) ENil tenv           = const $ extractingByNilIsNil tenv
extractSnd (ECons STrue _us1) (ECons STrue _us2) ENil = id
extractSnd (ECons STrue us1)  (ECons STrue us2) (ECons _ tenv) = \(ECons x xs) -> ECons x $ extractSnd us1 us2 tenv xs
extractSnd (ECons STrue _us1) (ECons SFalse _us2) ENil = id
extractSnd (ECons STrue us1) (ECons SFalse us2) (ECons _ tenv)
  = \(ECons _ xs) -> extractSnd us1 us2 tenv xs
extractSnd (ECons SFalse _us1) (ECons STrue _us2) ENil = id
extractSnd (ECons SFalse us1) (ECons STrue us2) (ECons _ tenv)
  = \(ECons x xs) -> ECons x $ extractSnd us1 us2 tenv xs
extractSnd (ECons SFalse _us1) (ECons SFalse _us2) ENil = id
extractSnd (ECons SFalse us1) (ECons SFalse us2) (ECons _ tenv)
  = extractSnd us1 us2 tenv

mergeUses ::
  Env SBool us1 -> Env SBool us2
  -> Env SBool (MergeUses us1 us2)
mergeUses ENil us           = us
mergeUses (ECons u us) ENil = ECons u us
mergeUses (ECons u1 us1) (ECons _u2 us2) = case u1 of
  STrue  -> ECons STrue (mergeUses us1 us2)
  SFalse -> ECons _u2   (mergeUses us1 us2)

keepElem :: (Env f as -> Env f bs) -> Env f (a ': as) -> Env f (a ': bs)
keepElem f (ECons x xs) = ECons x (f xs)

dropElem :: (Env f as -> Env f bs) -> Env f (a ': as) -> Env f bs
dropElem f (ECons _ xs) = f xs

newtype RearrEnv as us us' =
  RearrEnv { rearrEnv :: forall f. Env f (Extr as us) -> Env f (Extr as us') }

mergeTupled ::
  forall us1 us2 as f.
  Env SBool us1 -> Env SBool us2 -> Env Proxy as
  -> (Env SBool (MergeUses us1 us2),
      RearrEnv as (MergeUses us1 us2) us1,
      RearrEnv as (MergeUses us1 us2) us2)
mergeTupled ENil us2 tenv           = (us2, RearrEnv $ const $ extractingByNilIsNil tenv, RearrEnv id)
mergeTupled (ECons u1 us1) ENil tenv = (ECons u1 us1, RearrEnv $ id, RearrEnv $ const $ extractingByNilIsNil tenv)
mergeTupled (ECons u1 us1) (ECons u2 us2) ENil = (mergeUses (ECons u1 us1) (ECons u2 us2), RearrEnv id, RearrEnv id)
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





data IFqTEU as b =
  forall cs us1 us2.
  IFqTEU
      (Env Proxy as)
      (Conn Proxy cs)
      (Env SBool us1)
      (Env PackedCode (Extr as us1) -> CodeC (Code b, Conn PackedCode cs))
      (Env SBool us2)
      (Env PackedCode (Extr as us2) -> Env PackedCodeDelta (Extr as us2)-> Conn PackedCode cs -> CodeC (Code (Delta b), Conn PackedCode cs))

instance Term IFq IFqTEU where
  mapTerm (IFq sh2 f2 tr2)
          (IFqTEU tenv sh1 uf1 f1 utr1 tr1) = IFqTEU tenv (joinConn sh1 sh2) uf1 f utr1 tr
    where
      f a = do
        (b, c1) <- f1 a
        (c, c2) <- f2 b
        return (c, joinConn c1 c2)

      tr a da cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (db, c1') <- tr1 a da c1
        (dc, c2') <- tr2 db c2
        return (dc, joinConn c1' c2')

  multTerm :: forall as a b. IFqTEU as a -> IFqTEU as b -> IFqTEU as (a, b)
  multTerm (IFqTEU tenv sh1 uf1 f1 utr1 tr1) (IFqTEU _ sh2 uf2 f2 utr2 tr2)
    = IFqTEU tenv (joinConn sh1 sh2) uf f utr tr
    where
      (uf, extf1, extf2) = mergeTupled uf1 uf2 tenv

      f s = do
        (a, c1) <- f1 (rearrEnv extf1 s)
        (b, c2) <- f2 (rearrEnv extf2 s)
        r <- mkLet [|| ($$a, $$b) ||]
        return (r , joinConn c1 c2)

      (utr, exttr1, exttr2) = mergeTupled utr1 utr2 tenv

      tr s ds cc | (c1, c2) <- decompConn (isNone sh1) (isNone sh2) cc = do
        (da, c1') <- tr1 (rearrEnv exttr1 s) (rearrEnv exttr1 ds) c1
        (db, c2') <- tr2 (rearrEnv exttr2 s) (rearrEnv exttr2 ds) c2
        r <- mkLet [|| pairDelta $$da $$db ||]
        return ( r, joinConn c1' c2' )

  unitTerm tenv = IFqTEU tenv CNone ENil (\_ -> return ([|| () ||], CNone)) ENil (\_ _ _ -> return ([|| mempty ||], CNone))

  var0Term tenv = IFqTEU (ECons Proxy tenv)
                         CNone
                         (ECons STrue ENil)
                         (\(ECons (PackedCode a) _) -> return (a, CNone))
                         (ECons STrue ENil)
                         (\_ (ECons (PackedCodeDelta da) _) _ -> return (da, CNone))
  weakenTerm (IFqTEU tenv sh uf f utr tr) = IFqTEU (ECons Proxy tenv) sh (ECons SFalse uf) f (ECons SFalse utr) tr

  unliftTerm :: forall a b. Diff a =>  IFqTEU '[a] b -> IFq a b
  unliftTerm (IFqTEU _ (sh :: Conn Proxy cs) (uf :: Env SBool us1) f (utr :: Env SBool us2) tr) = IFq sh' f' tr'
    where
      sh' :: Conn Proxy (CSing cs '[a] us2)
      sh' = case utr of
        ENil           -> sh
        ECons SFalse _ -> sh
        ECons STrue  _ -> joinConn (CNE (COne (Proxy @a))) sh

      f' :: Code a -> CodeC (Code b, Conn PackedCode (CSing cs '[a] us2))
      f' a =
        case uf of
          ENil           -> conv =<< f ENil
          ECons SFalse _ -> conv =<< f ENil
          ECons STrue  _ -> conv =<< f (ECons (PackedCode a) ENil)
        where
          conv :: (Code b, Conn PackedCode cs) -> CodeC (Code b, Conn PackedCode (CSing cs '[a] us2))
          conv (b, c) = case utr of
            ENil           -> return (b, c)
            ECons SFalse _ -> return (b, c)
            ECons STrue  _ -> return (b, joinConn (CNE (COne (PackedCode a))) c)

      tr' da cc = case utr of
        ENil           -> tr ENil ENil cc
        ECons SFalse _ -> tr ENil ENil cc
        ECons STrue _  ->
          case decompConn (IsNoneFalse :: IsNone ('NE ('NEOne a))) (isNone sh) cc of
            (CNE (COne (PackedCode a)), c) -> do
              (db, c') <- tr (ECons (PackedCode a) ENil) (ECons (PackedCodeDelta da) ENil) c
              return (db, joinConn (CNE (COne (PackedCode [|| $$a /+ $$da ||]))) c')


type family CSing (cs :: Tree k) (as :: [k]) (bs :: [Bool]) :: Tree k where
  CSing cs '[] _ = cs
  CSing cs (_ ': _) '[] = cs
  CSing cs (a ': _) ('True  ': _) = Join ('NE ('NEOne a)) cs
  CSing cs (_ ': _) ('False ': _) = cs

type family SafeTail (as :: [k]) :: [k] where
  SafeTail '[] = '[]
  SafeTail (a ': as) = as

instance LetTerm IFq IFqTEU where
  letTerm :: forall as a b. Diff a => IFqTEU as a -> IFqTEU (a ': as) b -> IFqTEU as b
  letTerm (IFqTEU tenv (sh1 :: Conn Proxy cs1) (uf1 :: Env SBool usf1) f1 (utr1 :: Env SBool ustr1) tr1)
          (IFqTEU _    (sh2 :: Conn Proxy cs2) (uf2 :: Env SBool usf2) f2 (utr2 :: Env SBool ustr2) tr2)
    = IFqTEU tenv sh uf f utr tr
    where
      tenvA :: Env Proxy (a : as)
      tenvA = ECons Proxy tenv

      sh12 :: Conn Proxy (Join cs1 cs2)
      sh12 = joinConn sh1 sh2

      sh :: Conn Proxy (CSing (Join cs1 cs2) (a : as) ustr2)
      sh = case utr2 of
        ENil           -> sh12
        ECons SFalse _ -> sh12
        ECons STrue  _ -> joinConn (CNE (COne (Proxy @a))) sh12

      uf    :: Env SBool (MergeUses usf1 (SafeTail usf2))
      extf1 :: RearrEnv as (MergeUses usf1 (SafeTail usf2)) usf1
      extf2 :: RearrEnv as (MergeUses usf1 (SafeTail usf2)) (SafeTail usf2)

      (uf, extf1, extf2) = mergeTupled uf1 (tail' uf2) tenv

      tail' :: Env f xs -> Env f (SafeTail xs)
      tail' ENil         = ENil
      tail' (ECons _ xs) = xs

      f :: Env PackedCode (Extr as (MergeUses usf1 (SafeTail usf2)))
           -> CodeC (Code b, Conn PackedCode (CSing (Join cs1 cs2) (a : as) ustr2))
      f env = do
        (a, c1) <- f1 (rearrEnv extf1 env)
        (b, c2) <- f2 (ext a env)
        let c = joinConn c1 c2
        conv a (b, c)
        where
          ext :: Code a -> Env PackedCode (Extr as (MergeUses usf1 (SafeTail usf2))) -> Env PackedCode (Extr (a : as) usf2)
          ext a ev = case uf2 of
            ENil           -> ENil
            ECons SFalse _ -> rearrEnv extf2 ev
            ECons STrue  _ -> ECons (PackedCode a) (rearrEnv extf2 ev)

          conv :: Code a -> (Code b, Conn PackedCode (Join cs1 cs2)) -> CodeC (Code b, Conn PackedCode (CSing (Join cs1 cs2) (a : as) ustr2))
          conv a (b, c) = case utr2 of
            ENil           -> return (b, c)
            ECons SFalse _ -> return (b, c)
            ECons STrue  _ -> return (b, joinConn (CNE (COne (PackedCode a))) c)

      utr    :: Env SBool (MergeUses ustr1 (SafeTail ustr2))
      exttr1 :: RearrEnv as (MergeUses ustr1 (SafeTail ustr2)) ustr1
      exttr2 :: RearrEnv as (MergeUses ustr1 (SafeTail ustr2)) (SafeTail ustr2)

      (utr, exttr1, exttr2) = mergeTupled utr1 (tail' utr2) tenv

      tr ::
        Env PackedCode (Extr as (MergeUses ustr1 (SafeTail ustr2)))
        -> Env PackedCodeDelta (Extr as (MergeUses ustr1 (SafeTail ustr2)))
        -> Conn PackedCode (CSing (Join cs1 cs2) (a : as) ustr2)
        -> CodeC (Code (Delta b), Conn PackedCode (CSing (Join cs1 cs2) (a : as) ustr2))
      tr env denv c0 = case utr2 of
        ENil -> do
          let (c1, c2) = decompConn (isNone sh1) (isNone sh2) c0
          (_da, c1') <- tr1 (rearrEnv exttr1 env) (rearrEnv exttr1 denv) c1
          (db,  c2') <- tr2 (extractingByNilIsNil tenvA) (extractingByNilIsNil tenvA) c2
          return (db, joinConn c1' c2')
        ECons SFalse _ -> do
          let (c1, c2) = decompConn (isNone sh1) (isNone sh2) c0
          (_da, c1') <- tr1 (rearrEnv exttr1 env) (rearrEnv exttr1 denv) c1
          (db,  c2') <- tr2 (rearrEnv exttr2 env) (rearrEnv exttr2 denv) c2
          return (db, joinConn c1' c2')
        ECons STrue _ -> do
          let (CNE (COne (PackedCode a)), cc) = decompConn (IsNoneFalse :: IsNone ('NE ('NEOne a))) (isNone sh12) c0
          let (c1, c2) = decompConn (isNone sh1) (isNone sh2) cc
          (da, c1') <- tr1 (rearrEnv exttr1 env) (rearrEnv exttr1 denv) c1
          (db, c2') <- tr2 (ext (PackedCode a) env) (ext (PackedCodeDelta da) denv) c2
          a' <- mkLet [|| $$a /+ $$da ||]
          return (db, joinConn (CNE (COne (PackedCode a')))$ joinConn c1' c2')

        where
          ext  :: ff a -> Env ff (Extr as (MergeUses ustr1 (SafeTail ustr2))) -> Env ff (Extr (a : as) ustr2)
          ext x ev = case utr2 of
            ENil           -> ENil
            ECons SFalse _ -> rearrEnv exttr2 ev
            ECons STrue  _ -> ECons x (rearrEnv exttr2 ev)
