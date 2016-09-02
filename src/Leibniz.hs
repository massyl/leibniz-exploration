{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module Leibniz  where

data Dynamic rep where {
(:::) :: a -> rep a -> Dynamic rep
  
                       }
{--
  Leibniz type equality encoding. a, b are considered equal if they have the
  same properties.
  Leibniz law : a = b = forall p. p a <=> p b
  Our encoding of this definition is correct because the only conversion function
  that can be used with `Equal` data constructor is `id` as we don't have any
  information on the type constructor `f` because it's existentially qualified.
 --}
newtype Equal a b = Equal {unEqual :: forall f. f a -> f b}

{--
 Substitute any `a` in `x` by `b`. `y` is `x` with all `a` substituted by `b`
 Given any types `x` and `y` if you know how to turn `x` to `f a` (f type constuctor that take `a` as the last parameter) and you know how to turn `f b` to `y`
and you know that `a` is equal to `b` (Equal a b) then this function gives you a
function that turns `x` t0 `y`.
In other words : If you know how to abstract all `a` in x using a type constructor `f` (x <=> f a)  and you know that `a` equal to `b` (Equal a b) then you can
 substitute all `a` in `x` by `b`. We need to convert `x` to `f a` as the only conversion function we hold is (f a -> f b) given by `Equal a b`
--}
subst :: (x -> f a) -> (f b -> y) -> Equal a b -> x -> y
subst from to ab = to . unEqual ab . from

{--
 Data type used to flip the position of `a` and `b` in `Equal` type.
as we know how to substitute only the last type parameter of a type constructor as
 given by (forall f. f a -> f b). Thus we need to put the parameter that we need
 to substitute at the end (last position)
--}
newtype FlipEqual b a = Flip { unFlip :: Equal a b}

{--
 Type equality represents an Equivalence relation. the type `Equal` represent an
 Equivalence relation as we will witness below.
 1. Reflexivity
 2. Symetry
 3. Transitity
--}

refl :: Equal a a
refl = Equal id

sym :: Equal a b -> Equal b a
sym ab = subst Flip unFlip ab $ refl

trans :: Equal a b -> Equal b c -> Equal a c
trans (Equal ab) (Equal bc) = Equal $ bc . ab

trans' :: Equal a b -> Equal b c -> Equal a c
trans' ab bc=  unEqual bc ab

newtype Compose g f a = Comp {unComp :: g (f a)}
lift :: Equal a b -> Equal (f a) (f b)
lift  ab = Equal $ subst Comp unComp ab

rewrite :: Equal a b -> Equal c (f a) -> Equal c (f b)
rewrite ab cfa = trans cfa $ lift ab

newtype Gaf g a f = Gaf {unGaf :: g (f a)}
reshap :: Equal f g -> Equal (f a) (g a)
reshap fg = Equal $ subst Gaf unGaf fg

rewrite2 :: Equal a b -> Equal c (f a d) -> Equal c (f b d)
rewrite2 ab cfad = trans cfad $ reshap $ lift ab

rewrite3 :: Equal a b -> Equal c (f a d e) -> Equal c (f b d e)
rewrite3 ab cfad = trans cfad $ reshap $ reshap $ lift ab

congruence :: Equal a b -> Equal c d -> Equal (f a c) (f b d)
congruence ab cd = rewrite cd $ rewrite2 ab refl

deduce :: Equal x (a -> b)
       -> Equal y (c -> d)
       -> Equal a c
       -> Equal b d
       -> Equal x y
deduce xab ycd ac bd = trans xab $ trans (congruence ac bd) (sym ycd)       
          

  
---------------------------------------------------------------------------------
-- Using subst to express any substitution we want
---------------------------------------------------------------------------------

data Pair a = Pair {unPair :: (a, a)}
substPair :: Equal a b -> (a, a) -> (b, b)
substPair = subst Pair unPair

data Middle a b c = Middle {unMiddle :: (a, c, b)}
substMiddle :: Equal b d -> (a, b, c) -> (a, d, c)
substMiddle bd = subst Middle unMiddle bd

listRewrite :: Equal a Int -> Equal b [a] -> Equal b [Int]
listRewrite = rewrite
