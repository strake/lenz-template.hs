{-# LANGUAGE ViewPatterns, TemplateHaskell #-}

module Data.Lens.TH (mkLens) where

import Prelude hiding (concat, concatMap, foldr, foldl, foldl1)

import Control.Applicative
import Control.Arrow
import Control.Category.Unicode
import Control.Monad
import Data.Bool (bool)
import Data.Function (on)
import Data.Lens
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Data.Foldable
import Data.Foldable.Unicode
import Data.Traversable
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

reifyTyConDec :: Name -> Q ([TyVarBndr], [Con])
reifyTyConDec =
    fmap (\ case TyConI (DataD    _ _ bs cs _) -> (bs, cs)
                 TyConI (NewtypeD _ _ bs c  _) -> (bs, [c])
                 _ -> error "name of no simple type constructor") ∘ reify

mkLens :: ([Char] -> [Char]) -> Name -> Q [Dec]
mkLens name v0 =
    reifyTyConDec v0 >>= \ (bs@(fmap binderName -> vs0), cs) ->
    let labels :: [((Name, Type), [Name])]
        labels =
          (factorizeL ∘
           concatMap
           (\ case RecC v (fmap (\ (v, _, t) -> (v, t)) -> vts) -> flip (,) v <$> vts
                   _ -> [])) cs

        goT :: ((Name, Type), [Name]) -> Q Type
        goT ((v, t), us) =
          (\ vm ->
           ForallT (liftA2 List.union id (fmap (/. vm)) bs) [] $
           foldl1 AppT [ConT ''Data.Lens.Lens,
                        foldl AppT (ConT v0) (VarT <$> vs0),
                        foldl AppT (ConT v0) (VarT <$> (vs0 /. vm)),
                        t, t /. vm]) <$>
          foldrM (\ v m -> flip (Map.insert v) m <$> newName (nameBase v)) Map.empty (freeTypeVars t)

        goX :: ((Name, Type), [Name]) -> Q Exp
        goX ((v, t), us) =
          (\ (u, w) ->
           foldl1 AppE
           [VarE 'Data.Lens.lens,
            LamCaseE ((\ u -> Match (RecP u [(v, VarP w)]) (NormalB $ VarE w) []) <$> us),
            LamE [VarP w, VarP u] (RecUpdE (VarE u) [(v, VarE w)])]) <$> liftA2 (,) (newName "u") (newName "v")
    in (traverse
        ((\ l@((mkName ∘ name ∘ nameBase -> v, _), _) -> liftA3 (,,) (pure v) (goT l) (goX l)) &
         fmap (\ (v, t, x) -> [SigD v t, ValD (VarP v) (NormalB x) []])) & fmap concat) labels

freeTypeVars :: Type -> Set Name
freeTypeVars (ForallT (fmap binderName & Set.fromList -> vs) _ t) = freeTypeVars t `Set.difference` vs
freeTypeVars (AppT s t) = freeTypeVars s <> freeTypeVars t
freeTypeVars (SigT t _) = freeTypeVars t
freeTypeVars (VarT v) = Set.singleton v
freeTypeVars _ = Set.empty

binderName :: TyVarBndr -> Name
binderName (PlainTV v) = v
binderName (KindedTV v _) = v

class Functor' b a where fmap' :: (a -> a) -> b -> b

instance Functor' Type Name where
    fmap' f (ForallT bs@(fmap binderName & Set.fromList -> vs) c t) = ForallT bs c $ fmap' (liftA3 bool f id (∈ vs)) t
    fmap' f (AppT s t) = AppT (fmap' f s) (fmap' f t)
    fmap' f (SigT t k) = AppT (fmap' f t) k
    fmap' f (VarT v) = VarT (f v)
    fmap' f t = t

instance Functor' TyVarBndr Name where
    fmap' f (PlainTV v) = PlainTV (f v)
    fmap' f (KindedTV v k) = KindedTV (f v) k

instance Functor f => Functor' (f a) a where fmap' = fmap

(/.) :: (Ord a, Functor' b a) => b -> Map a a -> b
xs /. m = liftA2 fromMaybe id (flip Map.lookup m) `fmap'` xs

factorizeLBy :: (a -> a -> Bool) -> [(a, b)] -> [(a, [b])]
factorizeLBy (==) = List.groupBy ((==) `on` fst) & fmap (unzip >>> head *** id)

factorizeL :: (Eq a) => [(a, b)] -> [(a, [b])]
factorizeL = factorizeLBy (==)

infixr 9 &
(&) = flip (∘)
