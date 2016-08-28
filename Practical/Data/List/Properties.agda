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
  _∷_  : ∀ x {xs} → Finite xs → Finite (now (x ∷ xs))
  later : ∀ {xs} → ∃ (λ ys → (let open Equality {A = [ A ]'} (_≡_) in later xs ⇓ ys) × Finite (now ys)) → Finite (later xs)

-- 有限リストはWHNFを持つ(now hogeになる，neverではない)
Finite-has-whnf : ∀ {a} {A : Set a} {xss : [ A ]} → Finite xss →
                  ∃ λ whnf → let open Equality {A = [ A ]'} (_≡_) in xss ⇓ whnf
Finite-has-whnf [] = [] , Equality.now refl
Finite-has-whnf (_∷_ x {xs} _) = x ∷ xs , Equality.now refl
Finite-has-whnf (later {xs} (ys , xs⇓ys , fin)) = ys , xs⇓ys

module TestFinite where

  open PropEq using (_≢_; cong)
  open import Data.Nat
  open import Data.Product

  test-Finite-1 : Finite (later (♯ now (1 ∷ now [])))
  test-Finite-1 = later (1 ∷ _ , Equality.laterˡ (Equality.now refl) , 1 ∷ [])

  test-Finite-2 : Finite (later (♯ now (1 ∷ later (♯ now (2 ∷ now (3 ∷ now []))))))
  test-Finite-2 = later (1 ∷ _ , Equality.laterˡ (Equality.now refl) , 1 ∷ later (2 ∷ _ , Equality.laterˡ (Equality.now refl) , 2 ∷ (3 ∷ [])))

  -- 無限リストはどうか
  ones : [ ℕ ]
  ones = now (1 ∷ later (♯ ones))

  -- 無限リストに対しては示せない(今回の場合，停止性が)
  -- test-Finite-3 : Finite ones
  -- test-Finite-3 = ?

-- リストの無限性(ただし，無限に値が出てくるもの，つまり，neverではないことに注意)
data Infinite {a} {A : Set a} : [ A ] → Set a where
  _∷_  : ∀ x {xs} → (inf : Infinite xs) → Infinite (now (x ∷ xs))
  later : let open Equality {A = [ A ]'} (_≡_)
          in ∀ {xs} → (inf : ∃ (λ ys → later xs ⇓ ys × ∞ (Infinite (now ys)))) → Infinite (later xs)

-- 無限リストはWHNFを持つ(now hogeになる，neverではない)
Infinite-has-whnf : ∀ {a} {A : Set a} {xss : [ A ]} → Infinite xss →
                    ∃ λ whnf → let open Equality {A = [ A ]'} (_≡_) in xss ⇓ whnf
Infinite-has-whnf (_∷_ x {xs} inf) = x ∷ xs , Equality.now refl
Infinite-has-whnf (later {xs} (ys , xs⇓ys , inf)) = ys , xs⇓ys

module TestInfinite where

  open PropEq using (_≢_; cong)
  open import Data.Nat
  open import Data.Product

  -- 無限リストはどうか
  ones : [ ℕ ]
  ones = now (1 ∷ later (♯ ones))

  test-Infinite-1 : Infinite ones
  test-Infinite-1 = 1 ∷ later (1 ∷ _ , Equality.laterˡ (Equality.now refl) , ♯ test-Infinite-1)

  open import Relation.Nullary
  open import Data.Unit using (tt)
  open import Relation.Binary

  -- neverは無限リストではない
  test-Infinite-2 : ¬ Infinite (never {A  = [ ℕ ]'})
  test-Infinite-2 (later (proj₁ , proj₂ , proj₃)) = now≉never (Equivalence.sym PropEq.sym tt proj₂)

-- ある要素が含まれている
data _∈_ {a} {A : Set a} (x : A) : [ A ] → Set a where
  here  : ∀ {xs} → x ∈ now (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ now (y ∷ xs)
  later : ∀ {xs} → x ∈ ♭ xs → x ∈ later xs

module WithoutHang where

  open import Level using (_⊔_; suc)
  open import Data.Product
  open import Data.Sum

  -- 特定イベント列により，都度都度Hangしてないことを確かめられる
  -- たとえば，"\nECHO HELO\n"と打つといつでもHELOを出力してくれるみたいなイメージ
  -- インタラクティブ性として求められる性質はコレ
  Active : ∀ {a b} {A : Set a} {B : Set b} → ([ A ] → [ B ]) → Set (a ⊔ b)
  Active f = ∀ {xs}    →
             Finite xs →                 -- 任意のシーケンスの入力の後
             ∃ (λ as   →                 -- 特定のシーケンスの入力により
             ∃ (λ a    →                 -- ある特定の出力を
             a ∈ f (xs ++ as ++ never))) -- 発生させることができる

open WithoutHang public
