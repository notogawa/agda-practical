module Practical.Data.List.Properties where

open import Coinduction
open import Practical.Data.List
open import Category.Monad.Partiality hiding (map)

-- リストが有限であるという性質
module Finite {a ℓ} {A : Set a} (_∼_ : [ A ]' → [ A ]' → Set ℓ) where

  open import Level using (_⊔_)
  open Equality {A = [ A ]'} (_∼_)
  open import Data.Product

  data Finite : [ A ] → Set (a ⊔ ℓ) where
    []  : Finite (now [])
    _∷_  : ∀ x {xs} → (fin : Finite xs) → Finite (now (x ∷ xs))
    later : ∀ {xs} → (fin : ∃ (λ ys → later xs ⇓ ys × Finite (now ys))) → Finite (later xs)

module TestFinite where

  import Relation.Binary.PropositionalEquality as PropEq
  open PropEq using (_≡_; refl; _≢_; cong)
  open import Data.Nat
  open Finite {A = ℕ} (_≡_)
  open import Data.Product

  test-Finite-1 : Finite (later (♯ now (1 ∷ now [])))
  test-Finite-1 = later (1 ∷ _ , Equality.laterˡ (Equality.now PropEq.refl) , 1 ∷ [])

  test-Finite-2 : Finite (later (♯ now (1 ∷ later (♯ now (2 ∷ now (3 ∷ now []))))))
  test-Finite-2 = later (1 ∷ _ , Equality.laterˡ (Equality.now refl) , 1 ∷ later (2 ∷ _ , Equality.laterˡ (Equality.now refl) , 2 ∷ (3 ∷ [])))

  -- 無限リストはどうか
  ones : [ ℕ ]
  ones = now (1 ∷ later (♯ ones))

  -- 無限リストに対しては示せない(今回の場合停止性が)
  -- test-Finite-3 : Finite ones
  -- test-Finite-3 = 1 ∷ later (1 ∷ _ , Equality.laterˡ (Equality.now refl) , test-Finite-3)
  --
  -- だが，これは人の直観としては本来示せるべきもののようにも思われる？
  -- onesをcopatternsとかで定義できるなら示せる？
  -- 「コード生成を前提にしている以上，現時点ではFinite」？

module WithoutHang {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} (_∼_ : [ A ]' → [ A ]' → Set ℓ₁) (_≈_ : [ B ]' → [ B ]' → Set ℓ₂) where

  module FA = Finite {A = A} (_∼_)
  module FB = Finite {A = B} (_≈_)
  open import Level using (_⊔_)
  open import Data.Product
  open import Data.Sum

  -- 特定イベント列の投入により，出力が有限になる．
  -- たとえば，"\nQUIT\n"と打つといつでもそこで終わってくれるみたいなイメージ
  CanQuit : (f : [ A ] → [ B ]) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  CanQuit f = -- 任意の有限なpresと，(有限かどうかはわからない)postsに対し，
               ∀ {pres posts} → FA.Finite pres →
               -- 特定シーケンスを叩き込むと終了させることができる
               ∃ (λ probes → FB.Finite (f (pres ++ probes ++ posts)))

  -- 特定イベント列により，都度都度Hangしてないことを確かめられる
  -- たとえば，"\nHELO\n"と打つといつでも"WORLD"と出力してくれるみたいなイメージ
  -- インタラクティブ性として求められる性質はコレ
  Probable : (f : [ A ] → [ B ]) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  Probable f = -- 任意の有限なpresと，(有限かどうかはわからない)postsに対し，
               ∀ {pres posts} → FA.Finite pres →
               -- 特定シーケンスを叩き込むと何かを起こせる(presではHangしないことが観測できる)
               ∃ (λ probes → {!「f (pres ++ posts) と f (pres ++ probes ++ posts) で後者は何か要素が取り出せる状態になる」みたいな 考え中!})

  -- 任意の入力に対してHangしない
  -- headコマンドみたいなのに求められる性質
  Fin : (f : [ A ] → [ B ]) → Set (a ⊔ b ⊔ ℓ₂)
  Fin f = -- (有限かもわからない)任意の入力について，
          ∀ {xs} →
          -- 出力有限で終わる
          FB.Finite (f xs)

  -- 終わりまで読まないと結果が出せないけど，終わりまで読めるならHangしない
  -- sortコマンドみたいなのに求められる性質
  RequireAll : (f : [ A ] → [ B ]) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  RequireAll f = -- 任意の入力について，
                 ∀ {xs} →
                 -- 入力有限なら，
                 FA.Finite xs →
                 -- 出力有限で終わる
                 FB.Finite (f xs)
