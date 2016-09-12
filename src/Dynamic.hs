{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}

----------------------------------------------------------------------------------------------------
-- |
-- Module      : Dynamic
-- Copyright   : (C) 2016 Massyl Nait-Mouloud
-- License     : BSD-style
--
-- Maintainer  : Massyl Nait-Mouloud <massil.nait@gmail.com>
-- Stability   : experimental
-- Portability : ExistentialQualification, GADTs
--
-- Type safe cast of dynamic values represented by Dynamic data type to their types
-- the paper Typing Dynamic Typing http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.193.1552
--
----------------------------------------------------------------------------------------------------

module Dynamic (
  Dynamic,
  Comparable,
  TypeRepConst,
  TypeRep,
  coerce,
  fromDynamic,
  dynApply
 ) where

import Leibniz (Equal, subst, refl, sym, trans, substitute, deduce)
import Data.Functor.Identity
import Data.Functor(fmap)
import Control.Applicative((<$>), (<*>))
import Data.Maybe (fromJust)

data Dynamic rep where {
  (:::) :: a -> rep a -> Dynamic rep
}

class Comparable rep where {
  (<=>) :: rep a -> rep  b -> Maybe (Equal a b)
 }

data TypeRepConst a = Int (Equal a Int) | Bool ( Equal a Bool)
data TypeRep tpr a  = TypeConst (tpr a)
                 | forall x. List (Equal a [x])(TypeRep tpr x)
                 | forall x y. Func (Equal a (x -> y)) (TypeRep tpr x) (TypeRep tpr y)

type Type = TypeRep TypeRepConst                   
coerce :: Equal a b
       -> a
       -> b
coerce = subst Identity runIdentity

fromDynamic :: Comparable tpr => tpr a
             -> Dynamic tpr
             -> Maybe a
fromDynamic expected (a ::: actual) = (`coerce` a) <$> actual <=> expected


instance Comparable TypeRepConst where
  Int p1  <=> Int p2  = return $ trans p1 $ sym p2
  Bool p1 <=> Bool p2 = return $ trans p1 $ sym p2
  _ <=> _ = Nothing

instance Comparable tpr => Comparable (TypeRep tpr) where
  TypeConst x <=> TypeConst y = x <=> y
  List eq1 rep1 <=> List eq2 rep2 = trans eq1 . sym . (`substitute` eq2) <$> rep2 <=> rep1
  Func eqF arg1 res1 <=> Func eqG arg2 res2 = deduce eqF eqG <$> arg1<=>arg2 <*> res1<=>res2
  _ <=> _ = Nothing

infixr 5 .->
(.->) :: TypeRep tpr a -> TypeRep tpr b -> TypeRep tpr (a -> b)
tpra .-> tprb = Func refl tpra tprb

intTypeRepConst :: TypeRepConst Int
intTypeRepConst = Int refl

boolTypeRepConst :: TypeRepConst Bool
boolTypeRepConst = Bool refl

ten :: Dynamic TypeRepConst
ten = 10 ::: intTypeRepConst

true :: Dynamic TypeRepConst
true = True ::: boolTypeRepConst

intTypeRep :: Type Int
intTypeRep = TypeConst intTypeRepConst

boolTypeRep:: Type Bool
boolTypeRep = TypeConst boolTypeRepConst

listRep :: TypeRep tpr a -> TypeRep tpr [a]
listRep tpa = List refl tpa

intsToBool :: TypeRep TypeRepConst ([Int] -> Bool)
intsToBool = listRep intTypeRep .-> boolTypeRep

plusRep :: TypeRep TypeRepConst (Int -> Int -> Int)
plusRep = (intTypeRep .-> intTypeRep .-> intTypeRep)
plus :: Dynamic Type
plus = (+) ::: plusRep

one :: Dynamic (TypeRep TypeRepConst)
one = 1 ::: intTypeRep

twelve :: Dynamic (TypeRep TypeRepConst)
twelve = 12 ::: intTypeRep

thirteen :: Int
thirteen = fromJust $ fromDynamic plusRep plus <*> fromDynamic intTypeRep one <*> fromDynamic intTypeRep twelve

dynApply :: Comparable tpr => Dynamic (TypeRep tpr)
         -> Dynamic (TypeRep tpr)
         -> Maybe (Dynamic (TypeRep tpr))
dynApply (f:::frep) (x:::xrep)= case frep of
                                Func eqf arg res  ->
                                  (:::res) . coerce eqf f . (`coerce` x) <$> xrep<=>arg
                                _ -> Nothing

increment :: Dynamic Type
increment = fromJust $ dynApply plus one

successor :: Int -> Int
successor = fromJust $ fromDynamic (intTypeRep .-> intTypeRep) increment
