module Main where

import Leibniz (Equal, subst, substitute)
  
---------------------------------------------------------------------------------
-- Using subst to express any substitution we want
---------------------------------------------------------------------------------
newtype Pair a = Pair {unPair :: (a, a)}
substPair :: Equal a b -> (a, a) -> (b, b)
substPair = subst Pair unPair

newtype Middle a b c = Middle {unMiddle :: (a, c, b)}
substMiddle :: Equal b d -> (a, b, c) -> (a, d, c)
substMiddle bd = subst Middle unMiddle bd

listRewrite :: Equal a String -> Equal b [a] -> Equal b [String]
listRewrite = substitute

main :: IO ()
main = putStrLn "Nothing for now"
