{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}

module Dynamic where

import Leibniz (Equal, Equal(..), subst, refl, sym, trans, substitute,congruence)
import Data.Functor.Identity
import Control.Applicative(pure, (<$>), (<*>))

data Dynamic rep where {
  (:::) :: a -> rep a -> Dynamic rep
}

class MaybeLeibniz rep where {
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

fromDynamic :: MaybeLeibniz rep  => rep a
            -> Dynamic rep
            -> Maybe a
fromDynamic expected (a ::: actual) = case actual <=> expected of
                                Just eq -> return $ coerce eq a
                                _ -> Nothing

fromDynamic2 :: MaybeLeibniz tpr => tpr a
             -> Dynamic tpr
             -> Maybe a
fromDynamic2 expected (a ::: actual) = fmap (`coerce` a) $ actual <=> expected

instance MaybeLeibniz TypeRepConst where
  (Int p1)  <=> (Int p2)  = return $ trans p1 $ sym p2
  (Bool p1) <=> (Bool p2) = return $ trans p1 $ sym p2
  _ <=> _ = Nothing

instance MaybeLeibniz tpr => MaybeLeibniz (TypeRep tpr) where
  TypeConst x <=> TypeConst y = x <=> y
  List eq1 rep1 <=> List eq2 rep2 = trans eq1 . sym . (`substitute` eq2) <$> rep2 <=> rep1
  Func eqf repArg1 repRes1 <=> Func eqg repArg2 repRes2 = trans eqf . (`trans` sym eqg) <$> (congruence <$> repArg1<=>repArg2 <*> repRes1<=>repRes2)
    
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

-- (.->.)                          
