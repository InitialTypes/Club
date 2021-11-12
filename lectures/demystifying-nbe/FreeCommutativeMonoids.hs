{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
module FreeCommutativeMonoids where

  import Data.List

  import FreeMonoids

  enum :: (Bounded a, Enum a) => [a]
  enum = enumFromTo minBound maxBound

  newtype M x = M { unM :: x -> Int }

  instance Semigroup (M x) where
    M m1 <> M m2 = M $ \ x -> m1 x + m2 x
  instance Monoid (M x) where
    mempty = M $ \ x -> 0
  instance Eq x => MonoidOps M x where
    k x = M $ \ x' -> if x' == x then 1 else 0

  newtype N x = N { unN :: [x] } deriving (Semigroup, Monoid) -- OBS: not actually a commutative monoid without maintaining sortedness

  instance MonoidOps N x where
    k = N . pure

  instance (Bounded x, Enum x) => NormalForm M x where
    embNf (M m) = foldr (\ x -> \case { E -> K x; xs -> K x :*: xs }) E $ concatMap (\ x -> replicate (m x) x) $ filter ((>= 0) . m) enum

  instance Ord x => NormalForm N x where
    embNf (N n) = foldr (\ x -> \case { E -> K x; xs -> K x :*: xs }) E $ sort n

  -- norm :: forall x. (Bounded x, Enum x, Eq x) => Tm x -> Tm x
  -- norm t = embNf (eval t :: M x)
  norm :: forall x. Ord x => Tm x -> Tm x
  norm t = embNf (eval t :: N x)

  newtype MyFavouriteChars = MyFavouriteChars { unMyFavouriteChars :: Char } deriving (Eq, Enum, Ord)

  instance Show MyFavouriteChars where
    show = show . unMyFavouriteChars

  instance Bounded MyFavouriteChars where
    minBound = MyFavouriteChars 'a'
    maxBound = MyFavouriteChars 'z'

  fromToEnum :: (Enum a, Enum b) => a -> b
  fromToEnum = toEnum . fromEnum

  fromChar :: Enum a => Char -> a
  fromChar = fromToEnum

  t5 :: Tm MyFavouriteChars
  t5 = ((K (fromChar 'a') :*: E) :*: (E :*: (K (fromChar 'b') :*: K (fromChar 'a')))) :*: ((K (fromChar 'b') :*: K (fromChar 'a')) :*: E)
