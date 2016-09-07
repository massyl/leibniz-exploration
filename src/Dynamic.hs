{-# LANGUAGE GADTs #-}

module Dynamic where

import Leibniz (Equal, Equal(..), subst, refl, sym, trans)
import Data.Functor.Identity
import Data.Functor(fmap)

data Dynamic rep where {
  (:::) :: a -> rep a -> Dynamic rep
}

class TypeRep rep where {
  (<=>) :: rep a -> rep  b -> Maybe (Equal a b)
 }

data TpCon a = Int (Equal a Int) | Bool ( Equal a Bool)

coerce :: Equal a b
       -> a
       -> b
coerce = subst Identity runIdentity

fromDynamic :: TypeRep rep  => rep a
            -> Dynamic rep
            -> Maybe a
fromDynamic expected (a ::: actual) = case actual <=> expected of
                                Just eq -> return $ coerce eq a
                                _ -> Nothing

fromDynamic2 :: TypeRep tpr => tpr a
             -> Dynamic tpr
             -> Maybe a
fromDynamic2 expected (a ::: actual) = fmap (`coerce` a) $ actual <=> expected

instance TypeRep TpCon where
  (Int p1)  <=> (Int p2)  = return $ trans p1 $ sym p2
  (Bool p1) <=> (Bool p2) = return $ trans p1 $ sym p2
  _ <=> _ = Nothing


intRep :: TpCon Int
intRep = Int refl

boolRep :: TpCon Bool
boolRep = Bool refl

ten :: Dynamic TpCon
ten = 10 ::: intRep

true :: Dynamic TpCon
true = True ::: boolRep
