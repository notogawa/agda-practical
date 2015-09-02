-- uniqコマンド
--
-- $ agda -c -i. -i/usr/share/agda-stdlib/ example/uniq.agda
-- $ ./uniq
--
module example.uniq where

open import Practical hiding (String; _++_; toList)
open import IO
open import Function
open import Coinduction
open import Data.Maybe hiding (map)
open import Data.String hiding (unlines; fromList; _≟_)
open import Category.Monad.Partiality hiding (map)

uniq : [ String ] → [ String ]
uniq = go nothing where
  open import Relation.Binary
  open DecSetoid (Data.Maybe.decSetoid Data.String.decSetoid)
  open import Relation.Nullary
  go : Maybe String → [ String ] → [ String ]
  go mx (now []) = now []
  go mx (now (x ∷ xs)) with mx ≟ just x
  ... | yes _ = go mx xs
  ... | no  _ = now (x ∷ go (just x) xs)
  go mx (later x) = later (♯ go mx (♭ x))

main = run (interact (unlines ∘ map (fromList ∘ toList ∘ coloring) ∘ uniq ∘ lines)) where
  coloring : String → String
  coloring ss = "\x1b[32m" ++ ss ++ "\x1b[39m" -- わかりやすいように出力に色付け
