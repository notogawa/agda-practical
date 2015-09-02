module Practical.Data.String where

open import Coinduction
open import Category.Monad.Partiality hiding (map)
open import Practical.Data.List hiding (_++_)
open import Data.Char using (Char)
import Data.String as StdStr

String : Set
String = [ Char ] where

lines : String → [ StdStr.String ]
lines = go "" where
  open import Function
  open import Data.Product
  open import Relation.Nullary
  import Data.List
  go : StdStr.String → String → [ StdStr.String ]
  go acc (now []) = now (acc ∷ now [])
  go acc (now (x ∷ xs)) with x Data.Char.≟ '\n'
  ... | yes _ = now (acc ∷ go "" xs)
  ... | no  _ = later (♯ go (acc StdStr.++ StdStr.fromList Data.List.[ x ]) xs)
  go acc (later x) = later (♯ (go acc (♭ x)))

unlines : [ String ] → [ Char ]
unlines (now []) = now []
unlines (now (now [] ∷ xss)) = now ('\n' ∷ unlines xss)
unlines (now (now (x ∷ xs) ∷ xss)) = now (x ∷ unlines (now (xs ∷ xss)))
unlines (now (later xs ∷ xss)) = later (♯ unlines (now (♭ xs ∷ xss)))
unlines (later xss) = later (♯ unlines (♭ xss))
