{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}

-- | ITC 2021-02-04 Call-by-push-value
--   Andreas Abel
-------------------------------------------------------

import Control.Monad (ap, join)
import Data.Foldable (fold)

-- Haskell needs this to be happy:
instance Applicative Exp' where
  pure   = return
  (<*>)  = ap

-- * Monads
-------------------------------------------------------

-- | A variant of Hutton's razor.

data Exp' a
  = Leaf a
  | Plus (Exp' a) (Exp' a)
  -- -- | Lambda (Exp' (Maybe a))
  deriving (Eq, Show, Functor, Foldable, Traversable)

type Var = String
type Exp = Exp' Var

-- | Substitution.

subst :: Exp' a -> (a -> Exp' b) -> Exp' b
subst (Leaf a)     f = f a
subst (Plus e1 e2) f = Plus (subst e1 f) (subst e2 f)

instance Monad Exp' where
  return = Leaf
  (>>=)  = subst

joinExp :: Exp' (Exp' a) -> Exp' a
joinExp (Leaf e)     = e
joinExp (Plus e1 e2) = Plus (joinExp e1) (joinExp e2)

substExp :: (a -> Exp' b) -> Exp' a -> Exp' b
substExp f = joinExp . fmap f

-- Monad laws:
--
-- (outer unit)  join . return      = id          : T a → T a
-- (inner unit)  join . fmap return = id          : T a → T a
-- (assoc)       join . fmap join   = join . join : T³ a → T a

-- * Monad algebras
-------------------------------------------------------

-- | Evaluation.

runNum :: Num a => Exp' a -> a
runNum (Leaf n)     = n
runNum (Plus e1 e2) = runNum e1 + runNum e2

runStr :: Exp' String -> String
runStr (Leaf s)     = s
runStr (Plus e1 e2) = runStr e1 ++ runStr e2

runMon :: Monoid m => Exp' m -> m
runMon = fold

-- Exp'-algebra:  (N :: Type, run :: Exp' N → N)
-- (Inverse of return :: N → Exp' N)

-- Monad algebra laws:
-- Recipe: replace inner  (T a) by N  and  join : T² a → T a  by  run : T N → N

-- run . return   = id         : N → N
-- /
-- run . fmap run = run . join : T² N → N

-- - Any "monadic type" is a monad algebra (T a, join : T² a → T a)
-- - An IO-algebra would be (N, runIO :: IO N → N)

-- - A monad algebra generalizes the monad.

class Monad m => MonadAlgebra m n where
  run :: m n -> n

bind  :: Monad m          => m a -> (a -> m b) -> m b
bind  m f = join $ fmap f m

bindN :: MonadAlgebra m n => m a -> (a -> n  ) -> n
bindN m f = run  $ fmap f m

instance (MonadAlgebra m n1, MonadAlgebra m n2) => MonadAlgebra m (n1, n2) where
  run :: m (n1, n2) -> (n1, n2)
  run m = (run $ fmap fst m, run $ fmap snd m)

instance (MonadAlgebra m n) => MonadAlgebra m (p -> n) where
  run :: m (p -> n) -> p -> n
  run m p = run $ fmap ($ p) m

-- instance (MonadAlgebra m n1, MonadAlgebra m n2) => MonadAlgebra m (Either n1 n2) where
--   run :: m (Either n1 n2) -> Either n1 n2
--   run m = either

class Comonad d where
  extract :: d a -> a
  display :: d a -> d (d a)

-- instance Comonad (i,) where
--   extract (i,a) = a
--   display (i,a) = (i,(i,a))

-- instance Monoid j => Comonad (j ->) where
--   extract f = f mempty
--   display f = \ j1 -> \ j2 -> f (j1 <> j2)

class (Functor d, Comonad d) => ComonadCoalgebra d p where
  expose :: p -> d p

instance (ComonadCoalgebra d p1, ComonadCoalgebra d p2) => ComonadCoalgebra d (Either p1 p2) where
  expose :: Either p1 p2 -> d (Either p1 p2)
  expose = either (fmap Left . expose) (fmap Right . expose)
