{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}

----------------------------------------------------------------------------------------------------
-- |
-- Module      : Leibniz
-- Copyright   : (C) 2016 Massyl Nait-Mouloud
-- License     : BSD-style
--
-- Maintainer  : Massyl Nait-Mouloud <massil.nait@gmail.com>
-- Stability   : experimental
-- Portability : polykinds, rankNtypes, type famillies
--
-- The code in this module is inspired by http://okmij.org/ftp/Haskell/LeibnizInjective.hs and
-- the paper Typing Dynamic Typing http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.193.1552
--
----------------------------------------------------------------------------------------------------

module Leibniz (
 -- * Substitution functions
 subst,
 substitute,
 substitute2,
 substitute3,
 -- * Leibniz quality data type
 Equal,
 -- * Witnesses that Leibniz equality form equivalence relation
 refl,
 sym,
 trans,
 -- * lifting Leibniz equality
 lift,
 -- * Substitution on type constructor level
 reshap,
 -- * Witness of congruence relation of Leibniz equality regarding single parameter type constructor (Functor for instance)
 congruence,
 -- * Witness for deduction system using Leibniz equality. From some assumptions deduce (infer) new equality proofs
 deduce,
 -- * Witness of the injectivity of Leibniz equality
 injective,
 injective',
 injectiveArrow
 ) where

import Data.Functor.Identity
import qualified Control.Category as C

-------------------------------------------------------------------------------------       
-- |
-- Leibniz type equality encoding. a, b are considered equal if they have the
-- same properties.
-- Leibniz law : a = b = forall p. p a <=> p b
-- Our encoding of this definition is correct because the only conversion function
-- that can be used with `Equal` data constructor is `id` as we don't have any
-- information on the type constructor `f` because it's existentially qualified.
-------------------------------------------------------------------------------------
newtype Equal a b = Equal {unEqual :: forall f. f a -> f b}

---------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- |
-- Substitute any `a` in `x` by `b`. `y` is `x` with all `a` substituted by `b`
-- Given any types `x` and `y` if you know how to turn `x` to `f a` (f type constuctor that take `a` as the last parameter) and you know how to turn `f b` to `y`
-- and you know that `a` is equal to `b` (Equal a b) then this function gives you a
-- function that turns `x` to `y`.
-- In other words : If you know how to abstract all `a` in x using a type constructor `f` (x <=> f a)  and you know that `a` equal to `b` (Equal a b) then you can
-- substitute all `a` in `x` by `b`. We need to convert `x` to `f a` as the only conversion function we hold is (f a -> f b) given by `Equal a b`
---------------------------------------------------------------------------------------------------------------------------------------------------------------------
subst :: (x -> f a) -> (f b -> y) -> Equal a b -> x -> y
subst from to ab = to . unEqual ab . from

---------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- |
-- Data type used to flip the position of `a` and `b` in `Equal` type.
-- as we know how to substitute only the last type parameter of a type constructor as
-- given by (forall f. f a -> f b). Thus we need to put the parameter that we need
-- to substitute at the end (last position)
---------------------------------------------------------------------------------------------------------------------------------------------------------------------
newtype FlipEqual b a = Flip { unFlip :: Equal a b}

---------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- |
-- Type equality represents an Equivalence relation. the type `Equal` represent an
-- Equivalence relation as we will witness below.
-- 1. Reflexivity
-- 2. Symetry
-- 3. Transitity
---------------------------------------------------------------------------------------------------------------------------------------------------------------------

-----------------------------------------------
-- |
-- Witness that Equal is reflexive (x R x)
-----------------------------------------------
refl :: Equal a a
refl = Equal id

---------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- |
-- Witness that Equal is symetric.
-- The get the intuition of this implementation :
-- If we have a witness that a = b (Equal a b), we can replace all `a` in any expression
-- by `b` without changing the meaning of the expression
-- 1. Start with the reflexivity : a = a
-- 2. then change the `a` on the left of sign to get `b = a`
-- As we know to substitute only the last argument of any type constructor we need to flip
-- first (a = a) and then apply our substitution (Equal a b) and the unflip to get our result
--------------------------------------------------------------------------------------------------------------------------------------------------------------------
sym :: Equal a b -> Equal b a
sym ab = subst Flip unFlip ab refl

-------------------------------------------------------------------------------------
-- |
-- Witness that Equal is Transitity
-------------------------------------------------------------------------------------
trans :: Equal a b -> Equal b c -> Equal a c
trans (Equal ab) (Equal bc) = Equal $ bc . ab

trans' :: Equal a b -> Equal b c -> Equal a c
trans' =  flip unEqual

-------------------------------------------------------------------------------------
-- |
-- Lifts `Equal a b` to `Equal (f a) (f b)` for any type constructor `f`
-------------------------------------------------------------------------------------
newtype Compose g f a = Comp {unComp :: g (f a)}
lift :: Equal a b -> Equal (f a) (f b)
lift  ab = Equal $ subst Comp unComp ab

-------------------------------------------------------------------------------------
-- |
-- If we know that `a = b` and we know that `c = f a` then
-- we can deduce that `c = f b`.
-- For example: If we know that `a = String` and (c = [a]) then we know
-- that (c = [String])
-------------------------------------------------------------------------------------
substitute :: Equal a b -> Equal c (f a) -> Equal c (f b)
substitute ab cfa = trans cfa $ lift ab

-------------------------------------------------------------------------------------
-- |
-- Substitutes the first parameter of type constructor with kind  (* -> * -> *)
-------------------------------------------------------------------------------------
substitute2 :: Equal a b -> Equal c (f a d) -> Equal c (f b d)
substitute2 ab cfad = trans cfad $ reshap $ lift ab

-------------------------------------------------------------------------------------
-- |
-- Substitutes the first parameter of type constructor with kind (* -> * -> * -> *)
-------------------------------------------------------------------------------------
substitute3 :: Equal a b -> Equal c (f a d e) -> Equal c (f b d e)
substitute3 ab cfad = trans cfad $ reshap $ reshap $ lift ab

-------------------------------------------------------------------------------------
-- |
-- Newtype just to put `f` at the last position in (g (f a)) in
-- order to rich it with our substitution function
-------------------------------------------------------------------------------------
newtype Gaf g a f = Gaf {unGaf :: g (f a)}
reshap :: Equal f g -> Equal (f a) (g a)
reshap fg = Equal $ subst Gaf unGaf fg

-------------------------------------------------------------------------------------
-- |
-- Defines a congruence for a given type constructor of kind (* -> * -> *)
-- This can be a congruence for BiFunctor
-------------------------------------------------------------------------------------
congruence :: Equal a b -> Equal c d -> Equal (f a c) (f b d)
congruence ab cd = substitute cd $ substitute2 ab refl

-------------------------------------------------------------------------------------
-- |
-- Some proofs that can be deducedl
-- x = a -> b
-- y = c -> d
-- a = c
-- b = d
-- => x = y
-------------------------------------------------------------------------------------
deduce :: Equal x (a -> b)
       -> Equal y (c -> d)
       -> Equal a c
       -> Equal b d
       -> Equal x y
deduce xab ycd ac bd = trans xab $ trans (congruence ac bd) (sym ycd)

-------------------------------------------------------------------------------------
-- |
-- Making Equal injectivity
-- Note that we can't achieve it Leibniz.
-- We use open type family to proof injectivity
-------------------------------------------------------------------------------------
type family Fst a :: *
type instance Fst (f a) = a
newtype EqualFst a b = EqualFst { unFst :: Equal (Fst a) (Fst b)}

injective :: (Fst (f a) ~ a) => Equal (f a) (g b) -> Equal a b
injective eq =  subst id unFst eq (EqualFst refl :: EqualFst (f a)(f a))

-------------------------------------------------------------------------------------
-- |
-- Note that the first solution is limited as we can't use type synonyms for example
-- type Fake a = Bool
-- eq_ni ::Equal (Fake Char) (Fake Char)
-- eq_ni = refl
-- eq_bad = injective eq_ni
-- • Couldn't match type ‘Bool’ with ‘f0 a’
--   Expected type: Equal (f0 a) (g0 b)
--     Actual type: Equal (Fake Char) (Fake Char)
-- • In the first argument of ‘injective’, namely ‘eq_ni’
--   In the expression: injective eq_ni
--   In an equation for ‘eq_bad’: eq_bad = injective eq_ni
-- • Relevant bindings include
-- eq_bad :: Equal a b
-------------------------------------------------------------------------------------
type family Fst2 a :: *
type instance Fst2 (f a b) = a

newtype EqualFst2 a b = EqualFst2{unFst2 :: Equal (Fst2 a) (Fst2 b)}

injective' ::(Fst2 (f a b) ~ a) => Equal (f a b) (g c d) -> Equal a c
injective' eq =  subst id unFst2 eq (EqualFst2 refl :: EqualFst2 (f a b)(f a b))

injectiveArrow :: Equal (a -> b) (c -> d) -> Equal a c
injectiveArrow = injective'

-------------------------------------------------------------------------------------
-- |
-- Witness that Equal form a category
-------------------------------------------------------------------------------------
instance C.Category Equal where
  id = refl
  (.)= flip trans
  
