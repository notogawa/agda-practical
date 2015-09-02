module Practical.Data.String where

open import Practical.Data.List hiding (_++_)
open import Data.Char using (Char)

String : Set
String = [ Char ] where

open import Function
open import Coinduction
open import Data.Maybe
open import Category.Monad.Partiality hiding (map)
open import Category.Monad.State
open import Category.Monad
open import IO using (IO)
open import Data.Unit using (⊤)
import Data.String as StdStr

module DoLikeNotation {l M} (monad : RawMonad {l} M) where
  open RawMonad monad
  bind-syntax = _>>=_
  syntax bind-syntax F (λ x → G) = ∣ x ← F ∣ G

module Dummy where

  takeLine : StateT String _⊥ (Maybe StdStr.String)
  takeLine = proj₁ M.<$> ((LS.get LM.>>= go) "") where
    open import Function
    open import Relation.Nullary
    open import Data.List using ([_])
    open import Data.Product
    -- モナドI/Fとかリフトとかのサンプル
    module S = RawIMonadState (StateTMonadState String (Category.Monad.Partiality.monad))
    module M = RawMonad S.monad
    module SS = RawIMonadState (StateTMonadState StdStr.String S.monad)
    module LS = RawIMonadState (LiftMonadState StdStr.String (StateTMonadState String (Category.Monad.Partiality.monad)))
    module LM = RawMonad LS.monad
    open DoLikeNotation LS.monad
    go : String → StateT StdStr.String (StateT String _⊥) (Maybe StdStr.String)
    go (now []) = SS.get LM.>>= LM.return ∘ flush where
      flush : StdStr.String → Maybe StdStr.String
      flush x with x StdStr.≟ ""
      ... | yes _ = nothing
      ... | no  _ = just x
    go (now (x ∷ xs)) with x Data.Char.≟ '\n'
    ... | yes _ = ∣ _ ← LS.put xs
                ∣ ∣ acc ← SS.get
                ∣ ∣ _ ← SS.put ""
                  ∣ LM.return (just acc)
    ... | no  _ = λ acc ss → later (♯ go xs (acc StdStr.++ StdStr.fromList Data.List.[ x ]) xs) -- 相性が悪い…こうせざるをえない
    --            ∣ _ ← LS.put xs
    --          ∣ ∣ acc ← SS.get
    --          ∣ ∣ _ ← SS.put (acc ++ fromList [ x ])
    --            ∣ go (♭ xs)
    -- でも結局関数合成なので，_>>=_で合成してしまうと適切に再帰をlaterで包めない！
    -- Partiality Monad では末尾再帰しか上手く扱えない
    go (later xs) = λ acc ss → later (♯ go (♭ xs) acc ss)

    -- PartialityT に至っては定義できない！
    --
    -- open import Data.Sum
    -- data PartialityT (M : Set → Set) (A : Set) : Set where
    --   now-or-later : M (A ⊎ PartialityT M A) → PartialityT M A
    --
    -- PartialityT is not strictly positive, because it occurs
    -- in the 4th argument to _⊎_
    -- in an argument to a bound variable
    -- in the type of the constructor now-or-later
    -- in the definition of PartialityT.
{-
lines : String → [ StdStr.String ]
lines = go ∘ Dummy.takeLine where
  open import Function
  open import Data.Product
  go : (Maybe StdStr.String × String) ⊥ → [ StdStr.String ]
  go (now (nothing , _)) = now []
  go (now (just x , xs)) = now (x ∷ go (Dummy.takeLine xs))
  go (later x) = later (♯ go (♭ x))
-}
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
