{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
module FreeMonoids where
  import Control.Monad
  import Data.Foldable

  -- Terms
  data Tm x where
    E     :: Tm x
    (:*:) :: Tm x -> Tm x -> Tm x
    K     :: x -> Tm x
    deriving (Eq, Show, Functor, Foldable)

  fresh :: x -> Tm x
  fresh = K

  subst :: (x -> Tm y) -> (Tm x -> Tm y)
  subst s = fold . fmap s

  instance Applicative Tm where
    pure  = return
    (<*>) = ap

  instance Monad Tm where
    return = fresh
    (>>=)  = flip subst

  newtype PP = PP { unPP :: String }

  instance Semigroup PP where
    l <> r = PP $ concat [ "(", unPP l, " • ", unPP r, ")" ]

  instance Monoid PP where
    mempty = PP "e"

  pp :: (Foldable t, Show x) => t x -> String
  pp = unPP . foldMap (PP . show)

  prettyPrint :: (Foldable t, Show x) => t x -> IO ()
  prettyPrint = putStrLn . pp

  -- Normal forms that are either unit or (right-associated) products of parameters
  data Nf x where
    Ne' :: Ne' x -> Nf x
    E'  :: Nf x
    deriving (Eq, Show, Functor, Foldable)

  data Ne' x where
    Ne     :: Ne x -> Ne' x
    (:**:) :: Ne x -> Ne' x -> Ne' x
    deriving (Eq, Show, Functor, Foldable)

  data Ne x where
    K' :: x -> Ne x
    deriving (Eq, Show, Functor, Foldable)

  -- Normal forms that are (right-associated) unit-terminated products of parameters
  data Nf' x where
    E''     :: Nf' x
    (:***:) :: x -> Nf' x -> Nf' x
    deriving (Eq, Show, Functor, Foldable)

  -- Embed normal forms into terms
  class NormalForm t x where
    embNf :: t x -> Tm x

  instance NormalForm Nf x where
    embNf E'      = E
    embNf (Ne' n) = embNe' n
      where
        embNe' :: Ne' x -> Tm x
        embNe' (Ne n)       = embNe n
        embNe' (n1 :**: n2) = embNe n1 :*: embNe' n2

        embNe :: Ne x -> Tm x
        embNe (K' x) = K x

  instance NormalForm Nf' x where
    embNf E''          = E
    embNf (x :***: xs) = K x :*: embNf xs

  -- Monoid operations
  class Monoid (t x) => MonoidOps t x where
    -- primitive
    k   :: x -> t x

    -- derived
    cons :: x -> t x -> t x
    cons x xs = k x <> xs

    snoc :: t x -> x -> t x
    snoc xs x = xs <> k x

  -- Tm supports the monoid ops.
  instance Semigroup (Tm x) where
    (<>) = (:*:)
  instance Monoid (Tm x) where
    mempty = E
  instance MonoidOps Tm x where
    k = K

  -- Nf supports the monoid ops.
  instance Semigroup (Ne' x) where
    Ne x         <> n = x  :**: n
    (n1 :**: n2) <> n = n1 :**: (n2 <> n)
  instance Semigroup (Nf x) where
    E'     <> n      = n
    n      <> E'     = n
    Ne' n1 <> Ne' n2 = Ne' $ n1 <> n2
  instance Monoid (Nf x) where
    mempty = E'
  instance MonoidOps Nf x where
    k = Ne' . Ne . K'

  -- Nf -> Nf supports the monoid ops.
  newtype D x = D { unD :: Nf x -> Nf x }
  instance Semigroup (D x) where
    D d <> D d' = D $ d . d'
  instance Monoid (D x) where
    mempty = D id
  instance MonoidOps D x where
    k x = D $ \case { E' -> Ne' $ Ne $ K' x; Ne' n -> Ne' $ K' x :**: n } -- = cons x :: Nf x -> Nf x

  -- [] supports the monoid ops.
  instance MonoidOps [] x where
    k = pure

  -- Interpretation of terms in a type that supports the monoid ops
  eval :: MonoidOps t x => Tm x -> t x
  eval E           = mempty
  eval (e1 :*: e2) = eval e1 <> eval e2
  eval (K x)       = k x

  -- Normalization
  norm :: Tm x -> Tm x
  norm = embNf . reify . eval
    where
      -- reify :: Nf x -> Nf x
      -- reify = id

      -- reify :: D x -> Nf x
      -- reify = ($ E') . unD

      -- >>> norm (K 0 :*: K 1)
      -- (:*:) (K 0) ((:*:) (K 1) E)
      reify :: [x] -> Nf' x
      reify = foldr (:***:) E''

  -- Examples
  t1 :: Tm Int
  t1 = (E :*: K 1) :*: (K 2 :*: (K 4 :*: (E :*: K 6)))

  t2 :: Tm Int
  t2 = (E :*: K 1) :*: (K 2 :*: ((E :*: K 4) :*: K 6))

  t3 :: Tm Int
  t3 = (E :*: K 1) :*: ((K 2 :*: K 5) :*: K 6)

  ex1 :: Bool
  ex1 = t1 /= t2 && norm t1 == norm t2

  ex2 :: Bool
  ex2 = t1 /= t3 && norm t1 /= norm t3
