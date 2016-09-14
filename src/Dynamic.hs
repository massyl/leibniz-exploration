{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}

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

import           Control.Applicative   ((<$>), (<*>))
import           Data.Functor          (fmap)
import           Data.Functor.Identity
import           Data.Maybe            (fromJust)
import           Leibniz               (Equal, deduce, refl, subst, substitute,sym, trans)
import           Control.Monad (join)

data Dynamic rep where {
  (:::) :: a -> rep a -> Dynamic rep
}

class Comparable rep where {
  (<=>) :: rep a -> rep  b -> Maybe (Equal a b)
 }

data TypeRepConst a = Int (Equal a Int) | Bool ( Equal a Bool)| String (Equal a String)
data TypeRep tpr a  = TypeConst (tpr a)
                 | forall x. List (Equal a [x])(TypeRep tpr x)
                 | forall x y. Func (Equal a (x -> y)) (TypeRep tpr x) (TypeRep tpr y)

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
  String p1 <=> String p2 = return $ trans p1 $ sym p2
  _ <=> _ = Nothing

instance Comparable tpr => Comparable (TypeRep tpr) where
  TypeConst x <=> TypeConst y = x <=> y
  List eq1 rep1 <=> List eq2 rep2 = trans eq1 . sym . (`substitute` eq2) <$> rep2 <=> rep1
  Func eqF arg1 res1 <=> Func eqG arg2 res2 = deduce eqF eqG <$> arg1<=>arg2 <*> res1<=>res2
  _ <=> _ = Nothing

infixr 5 .->
(.->) :: TypeRep tpr a -> TypeRep tpr b -> TypeRep tpr (a -> b)
tpra .-> tprb = Func refl tpra tprb

intRep :: TypeRep TypeRepConst Int
intRep = TypeConst $ Int refl 

boolTypeRep:: TypeRep TypeRepConst Bool
boolTypeRep = TypeConst $ Bool refl

listRep :: TypeRep tpr a -> TypeRep tpr [a]
listRep tpa = List refl tpa

intsToBool :: TypeRep TypeRepConst ([Int] -> Bool)
intsToBool = listRep intRep .-> boolTypeRep

plusRep :: TypeRep TypeRepConst (Int -> Int -> Int)
plusRep = (intRep .-> intRep .-> intRep)

plus :: Dynamic (TypeRep TypeRepConst)
plus = (+) ::: plusRep

one :: Dynamic (TypeRep TypeRepConst)
one = 1 ::: intRep

true :: Dynamic (TypeRep TypeRepConst)
true = True ::: boolTypeRep

twelve :: Dynamic (TypeRep TypeRepConst)
twelve = 12 ::: intRep

thirteen :: Int
thirteen = fromJust $ plus `dynApply` one >>= (`dynApply` twelve) >>= fromDynamic intRep

dynApply :: Comparable tpr => Dynamic (TypeRep tpr)
         -> Dynamic (TypeRep tpr)
         -> Maybe (Dynamic (TypeRep tpr))
dynApply (f:::frep) (x:::xrep)= case frep of
                                Func eqf arg res  -> (:::res) . coerce eqf f . (`coerce` x) <$> xrep<=>arg
                                _ -> Nothing

increment :: Dynamic (TypeRep TypeRepConst)
increment = fromJust $ dynApply plus one

successor :: Int -> Int
successor = fromJust $ fromDynamic (intRep .-> intRep) increment
