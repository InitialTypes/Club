{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
module FreeBooleanAlgebras where

import Control.Applicative
import Control.Monad
import Data.Functor
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

infixr 8 ∨, :∨:
infixr 9 ∧, :∧:

list :: b -> (a -> [a] -> b) -> [a] -> b
list n  _c []     = n
list _n c  (a:as) = c a as

enum :: (Bounded a, Enum a) => [a]
enum = enumFromTo minBound maxBound

class BooleanAlgebraOps m x where
  f   :: m x
  (∨) :: m x -> m x -> m x
  t   :: m x
  (∧) :: m x -> m x -> m x
  n   :: m x -> m x
  k   :: x -> m x

newtype Or m x = Or  { unOr  :: m x }

instance BooleanAlgebraOps m x => Semigroup (Or m x) where
  Or t1 <> Or t2 = Or $ t1 ∨ t2
instance BooleanAlgebraOps m x => Monoid (Or m x) where
  mempty  = Or f
  mappend = (<>)

newtype And m x = And { unAnd :: m x }

instance BooleanAlgebraOps m x => Semigroup (And m x) where
  And t1 <> And t2 = And $ t1 ∧ t2
instance BooleanAlgebraOps m x => Monoid (And m x) where
  mempty  = And t
  mappend = (<>)

data Tm x where
  F     :: Tm x
  (:∨:) :: Tm x -> Tm x -> Tm x
  T     :: Tm x
  (:∧:) :: Tm x -> Tm x -> Tm x
  N     :: Tm x -> Tm x
  K     :: x -> Tm x
  deriving (Eq, Functor)

instance Applicative Tm where
  pure  = K
  (<*>) = ap

instance Monad Tm where
  ma >>= k = j $ k <$> ma
    where
      j F           = F
      j (t1 :∨: t2) = j t1 :∨: j t2
      j T           = T
      j (t1 :∧: t2) = j t1 :∧: j t2
      j (N t)       = N $ j t
      j (K t)       = t

instance Show x => Show (Tm x) where
  showsPrec _p F           = showString "⊥"
  showsPrec  p (t1 :∨: t2) = let q = 8  in showParen (q /= p && p > 0) $ showsPrec q t1 . showString " ∨ " . showsPrec q t2
  showsPrec _p T           = showString "⊤"
  showsPrec  p (t1 :∧: t2) = let q = 9  in showParen (q /= p && p > 0) $ showsPrec q t1 . showString " ∧ " . showsPrec q t2
  showsPrec  p (N t)       = let q = 10 in showParen (q < p)           $ showString "¬ " . showsPrec q t
  showsPrec  p (K x)       = showsPrec p x

instance BooleanAlgebraOps Tm x where
  f = F

  F  ∨ t  = t
  t  ∨ F  = t
  t1 ∨ t2 = t1 :∨: t2

  t = T

  T  ∧ t  = t
  t  ∧ T  = t
  t1 ∧ t2 = t1 :∧: t2

  n = N

  k = K

eval :: BooleanAlgebraOps m x => Tm x -> m x
eval F           = f
eval (t1 :∨: t2) = eval t1 ∨ eval t2
eval T           = t
eval (t1 :∧: t2) = eval t1 ∧ eval t2
eval (N t)       = n $ eval t
eval (K x)       = k x

class Reifiable m x where
  reify :: m x -> Tm x

-- Disjunctions of conjunctions of literals

data    Literal x = Pos x | Neg x                                 deriving (Eq, Show, Ord)
newtype Product l = Product { unProduct  :: [l]                 } deriving (Eq, Show, Semigroup, Monoid, Foldable, Functor, Traversable, Applicative, Alternative, Monad, Ord)
newtype Sum     c = Sum     { unSum      :: [c]                 } deriving (Eq, Show, Semigroup, Monoid, Foldable, Functor, Traversable, Applicative, Alternative)
newtype Clause  x = Clause  { getClause  :: Product (Literal x) } deriving (Eq, Show, Semigroup, Monoid, Ord)
newtype DNF     x = DNF     { getClauses :: Sum (Clause x)      } deriving (Eq, Show, Semigroup, Monoid)

literal :: (x -> y) -> (x -> y) -> Literal x -> y
literal  p _n (Pos x) = p x
literal _p  n (Neg x) = n x

nLiteral :: Literal x -> Literal x
nLiteral = literal Neg Pos

nClause :: Clause x -> DNF x
nClause (Clause (Product ls)) = DNF $ Sum $ map (lClause . nLiteral) ls

kClause :: x -> Clause x
kClause = lClause . Pos

lClause :: Literal x -> Clause x
lClause = Clause . Product . singleton

distr :: Product (Sum a) -> Sum (Product a)
distr = sequenceA

instance Eq x => BooleanAlgebraOps DNF x where
  f                 = mempty
  f1 ∨ f2           = f1 <> f2
  t                 = DNF $ pure mempty
  DNF cs1 ∧ DNF cs2 = DNF $ Clause <$> join <$> distr (pure (cs1 <&> getClause) <|> pure (cs2 <&> getClause))
  n (DNF cs)        = unAnd $ foldMap (And . nClause) cs
  k x               = DNF $ pure $ kClause x

instance Reifiable Literal x where
  reify = literal K (N . K)

instance Reifiable Product l where
  reify = unAnd . foldMap (And . K)

instance Reifiable Sum c where
  reify = unOr . foldMap (Or . K)

instance Reifiable Clause x where
  reify = join . reify . fmap reify . getClause

instance Reifiable DNF x where
  reify = join . reify . fmap reify . getClauses

-- Full disjunctive normal form

newtype Row        x = Row        { getRow  :: Set x       } deriving (Eq, Show, Ord)
newtype TruthTable x = TruthTable { getRows :: Set (Row x) } deriving (Eq, Show)

rows :: (Bounded x, Enum x, Ord x) => Set (Row x)
rows = Set.map Row $ Set.powerSet $ Set.fromList enum

toClause :: (Bounded x, Enum x, Ord x) => Row x -> Clause x
toClause (Row r) = Clause $ Product $ map (\x -> if x `Set.member` r then Pos x else Neg x) enum

toDNF :: (Bounded x, Enum x, Ord x) => TruthTable x -> DNF x
toDNF (TruthTable t) = DNF $ Sum $ Set.toList $ Set.map toClause t

instance (Bounded x, Enum x, Ord x) => BooleanAlgebraOps TruthTable x where
  f                             = TruthTable Set.empty
  TruthTable t1 ∨ TruthTable t2 = TruthTable $ t1 `Set.union` t2
  t                             = TruthTable rows
  TruthTable t1 ∧ TruthTable t2 = TruthTable $ t1 `Set.intersection` t2
  n (TruthTable t)              = TruthTable $ rows `Set.difference` t
  k x                           = TruthTable $ Set.filter ((x `Set.member`) . getRow) rows

instance (Bounded x, Enum x, Ord x) => Reifiable TruthTable x where
  reify = reify . toDNF

-- Prime disjunctive normal form

-- Normalization
norm :: forall x. (Bounded x, Enum x, Ord x) => Tm x -> Tm x
norm = r . eval
  where
    -- r :: DNF x -> Tm x
    r :: TruthTable x -> Tm x
    -- r :: PNF x -> Tm x
    r = reify

-- Examples
newtype Atom = Atom { getAtom :: Int } deriving (Eq, Enum, Ord)

instance Show Atom where
  show (Atom n) = show n

instance Bounded Atom where
  minBound = Atom 1
  maxBound = Atom 2

t1 :: Tm Atom
t1 = K $ toEnum 1

t2 :: Tm Atom
t2 = t1 :∨: N t1

t3 :: Tm Atom
t3 = K (toEnum 2) :∨: (N (K $ toEnum 1) :∧: N (K $ toEnum 2))
