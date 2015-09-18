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
  later : let open Equality {A = [ A ]'} (_≡_)
          in ∀ {xs} → (fin : ∃ (λ ys → later xs ⇓ ys × Finite (now ys))) → Finite (later xs)

-- 有限リストはWHNFを持つ(now hogeになる，neverではない)
Finite-has-whnf : ∀ {a} {A : Set a} {xss : [ A ]} →
                  let open Equality {A = [ A ]'} (_≡_)
                  in Finite xss → ∃ λ whnf → xss ⇓ whnf
Finite-has-whnf [] = [] , Equality.now refl
Finite-has-whnf (_∷_ x {xs} fin) = x ∷ xs , Equality.now refl
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
  -- test-Finite-3 = 1 ∷ later (1 ∷ _ , Equality.laterˡ (Equality.now refl) , test-Finite-3)

-- リストの無限性(ただし，無限に値が出てくるもの，つまり，neverではないことに注意)
data Infinite {a} {A : Set a} : [ A ] → Set a where
  _∷_  : ∀ x {xs} → (inf : Infinite xs) → Infinite (now (x ∷ xs))
  later : let open Equality {A = [ A ]'} (_≡_)
          in ∀ {xs} → (inf : ∃ (λ ys → later xs ⇓ ys × ∞ (Infinite (now ys)))) → Infinite (later xs)

-- 無限リストはWHNFを持つ(now hogeになる，neverではない)
Infinite-has-whnf : ∀ {a} {A : Set a} {xss : [ A ]} →
                  let open Equality {A = [ A ]'} (_≡_)
                  in Infinite xss → ∃ λ whnf → xss ⇓ whnf
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

module WithoutHang {a b} (A : Set a) (B : Set b) where

  open import Level using (_⊔_)
  open import Data.Product
  open import Data.Sum

  -- 特定イベント列により，都度都度Hangしてないことを確かめられる
  -- たとえば，"\nQUIT\n"と打つといつでもそこで終わってくれるみたいなイメージ
  -- インタラクティブ性として求められる性質はコレ
  -- Probable : (f : [ A ] → [ B ]) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  -- Probable f = -- 任意の有限なpresと，(有限かどうかはわからない)postsに対し，
  --              ∀ {pres posts} → FA.Finite pres →
  --              -- 特定シーケンスを叩き込むと何かを起こせる(presではHangしないことが観測できる)
  --              ∃ (λ probes → {!「f (pres ++ posts) と f (pres ++ probes ++ posts) で後者は何か要素が取り出せる状態になる」みたいな 考え中!})

  -- 任意の入力に対してHangしない
  -- headコマンドみたいなのに求められる性質
  Fin : (f : [ A ] → [ B ]) → Set (a ⊔ b)
  Fin f = -- (有限かもわからない)任意の入力について，
          ∀ {xs} →
          -- 出力有限で終わる
          Finite (f xs)

  -- 終わりまで読まないと結果が出せないけど，終わりまで読めるならHangしない
  -- sortコマンドみたいなのに求められる性質
  RequireAll : (f : [ A ] → [ B ]) → Set (a ⊔ b)
  RequireAll f = -- 任意の入力について，
                 ∀ {xs} →
                 -- 入力有限なら，
                 Finite xs →
                 -- 出力有限で終わる
                 Finite (f xs)
