module Practical.Data.List.Properties where

open import Coinduction
open import Practical.Data.List
open import Category.Monad.Partiality hiding (map)
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl)
open import Data.Product

-- リストの有限性
data Finite {a} {A : Set a} : [ A ] → Set a where
  []  : Finite (now [])
  _∷_  : ∀ x {xs} → (fin : Finite xs) → Finite (now (x ∷ xs))
  later : ∀ {xs} → (term : let open Equality {A = [ A ]'} (_≡_) in (♭ xs) ⇓) → (fin : Finite (♭ xs)) → Finite (later xs)

-- 有限リストはWHNFを持つ(now hogeになる，neverではない)
Finite-has-whnf : ∀ {a} {A : Set a} {xs : [ A ]} → Finite xs →
                  ∃ λ whnf → let open Equality {A = [ A ]'} (_≡_) in xs ⇓ whnf
Finite-has-whnf [] = [] , Equality.now refl
Finite-has-whnf (_∷_ x {xs} _) = x ∷ xs , Equality.now refl
Finite-has-whnf (later term fin) with Finite-has-whnf fin
Finite-has-whnf (later term fin) | proj₁ , proj₂ = proj₁ , Equality.laterˡ proj₂
-- Finite-has-whnf (later term fin) with Finite-has-whnf fin
-- Finite-has-whnf (later term fin) | proj₁ , proj₂ = proj₁ , Equality.laterˡ proj₂

module TestFinite where

  open PropEq using (_≢_; cong)
  open import Data.Nat
  open import Data.Product

  test-Finite-1 : Finite (later (♯ now (1 ∷ now [])))
  test-Finite-1 = later (1 ∷ now [] , Equality.now refl) (1 ∷ [])

  test-Finite-2 : Finite (later (♯ now (1 ∷ later (♯ now (2 ∷ now (3 ∷ now []))))))
  test-Finite-2 = later ((1 ∷ _) , Equality.now refl ) (1 ∷ (later ((2 ∷ _) , Equality.now refl) (2 ∷ (3 ∷ []))))

  -- 無限リストはどうか
  ones : [ ℕ ]
  ones = now (1 ∷ later (♯ ones))

  -- 無限リストに対しては示せない(今回の場合，停止性が)
  -- test-Finite-3 : Finite ones
  -- test-Finite-3 = ?

-- リストの無限性(無限に値が出てくるものに限る．つまり，neverではないことに注意)
data Infinite {a} {A : Set a} : [ A ] → Set a where
  _∷_  : ∀ x {xs} → (inf : Infinite xs) → Infinite (now (x ∷ xs))
  later : ∀ {xs} → (term : let open Equality {A = [ A ]'} (_≡_) in (♭ xs) ⇓) → (inf : ∞ (Infinite (♭ xs))) → Infinite (later xs)

-- 無限リストはWHNFを持つ(now hogeになる，neverではない)
Infinite-has-whnf : ∀ {a} {A : Set a} {xss : [ A ]} → Infinite xss →
                    ∃ λ whnf → let open Equality {A = [ A ]'} (_≡_) in xss ⇓ whnf
Infinite-has-whnf (_∷_ x {xs} inf) = x ∷ xs , Equality.now refl
Infinite-has-whnf (later (proj₁ , proj₂) inf) = proj₁ , Equality.laterˡ proj₂

module TestInfinite where

  open PropEq using (_≢_; cong)
  open import Data.Nat
  open import Data.Product

  -- 無限リストはどうか
  ones : [ ℕ ]
  ones = now (1 ∷ later (♯ ones))

  test-Infinite-1 : Infinite ones
  test-Infinite-1 = 1 ∷ later ((1 ∷ _) , (Equality.now refl)) (♯ test-Infinite-1)

  open import Relation.Nullary
  open import Data.Unit using (tt)
  open import Relation.Binary

  -- neverは無限リストではない
  test-Infinite-2 : ¬ Infinite (never {A  = [ ℕ ]'})
  test-Infinite-2 (later (proj₁ , proj₂) inf) = now≉never (Equivalence.sym PropEq.sym tt proj₂)

-- 途中でStopする
data Stop {a} {A : Set a} : [ A ] → Set a where
  stop : Stop never
  _∷_  : ∀ x {xs} → Stop xs → Stop (now (x ∷ xs))
  later : ∀ {xs} → (term : let open Equality {A = [ A ]'} (_≡_) in (♭ xs) ⇓) → (hang : Stop (♭ xs)) → Stop (later xs)

output-before-stop : ∀ {a} {A : Set a} {xs : [ A ]} → Stop xs → [ A ]
output-before-stop stop = now []
output-before-stop (x ∷ h) = now (x ∷ output-before-stop h)
output-before-stop (later term h) = later (♯ output-before-stop h)

{-
output-before-stop-is-Finite : ∀ {a} {A : Set a} {xs : [ A ]} → (h : Stop xs) → Finite (output-before-stop h)
output-before-stop-is-Finite stop = []
output-before-stop-is-Finite (x ∷ h) = x ∷ output-before-stop-is-Finite h
output-before-stop-is-Finite (later term h) with output-before-stop-is-Finite h | PropEq.inspect output-before-stop-is-Finite h
... | a | b = ?
-}

-- ある要素が含まれている
data _∈_ {a} {A : Set a} (x : A) : [ A ] → Set a where
  here  : ∀ {xs} → x ∈ now (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ now (y ∷ xs)
  later : ∀ {xs} → x ∈ ♭ xs → x ∈ later xs

module WithoutStop where

  open import Level using (_⊔_; suc)
  open import Data.Product
  open import Data.Sum

  -- 特定イベント列により，都度都度ハングしてないことを確かめられる
  -- たとえば，"\nECHO HELO\n"と打つといつでもHELOを出力してくれるみたいなイメージ
  -- インタラクティブ性として求められる性質はコレ
  Probeable : ∀ {a b} {A : Set a} {B : Set b} → ([ A ] → [ B ]) → Set (a ⊔ b)
  Probeable f = ∀ {xs}    →
                Finite xs →                 -- 任意のシーケンスの入力の後
                (stop : Stop (f (xs ++ never))) →
                let xs' = output-before-stop stop in
                ∃ (λ as   →                 -- 特定のシーケンスの入力により
                ∃ (λ a    →                 -- ある特定の出力を
                a ∈ f (xs ++ as ++ never))) -- 発生させることができる
