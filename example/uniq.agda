-- uniqコマンド
module example.uniq where

open import Practical hiding (String; _++_; toList)
open import IO
open import Function
open import Coinduction
open import Data.Maybe hiding (map)
open import Data.String hiding (unlines; fromList; _≟_)
open import Category.Monad.Partiality hiding (map)
open import Relation.Binary
open DecSetoid (Data.Maybe.decSetoid Data.String.decSetoid)
open import Relation.Nullary

go : Maybe String → [ String ] → [ String ]
go mx (now []) = now []
go mx (now (x ∷ xs)) with mx ≟ just x
... | yes _ = go mx xs
... | no  _ = now (x ∷ go (just x) xs)
go mx (later x) = later (♯ go mx (♭ x))

uniq : [ String ] → [ String ]
uniq = go nothing

main = run (interact (unlines ∘ map (fromList ∘ toList ∘ coloring) ∘ uniq ∘ lines)) where
  coloring : String → String
  coloring ss = "\x1b[32m" ++ ss ++ "\x1b[39m" -- わかりやすいように出力に色付け

-- uniqの性質を証明してみよう
module Properties where

  import Relation.Binary.PropositionalEquality as PropEq
  open PropEq using (_≡_; refl; _≢_; cong)
  open Equality {A = [ String ]'} (_≡_)

  -- xss が空リストに評価される値ならば，uniq xssも空リストに評価される
  uniq[]-is-[] : ∀ xss → xss ⇓ [] → uniq xss ⇓ []
  uniq[]-is-[] ._ (Equality.now x∼y) rewrite x∼y = Equality.now PropEq.refl
  uniq[]-is-[] ._ (Equality.laterˡ {x = x} x₁) = Equality.laterˡ (uniq[]-is-[] (♭ x) x₁)

  -- 隣接2要素の値が異なるという性質 Uniq
  data Uniq : [ String ] → Set where
    nil : Uniq (now [])
    singleton : ∀ {xs} → Uniq (now (xs ∷ now []))
    cons : ∀ {xs ys yss} → xs ≢ ys → Uniq (now (ys ∷ yss))→ Uniq (now (xs ∷ now (ys ∷ yss)))
    later1 : ∀ {xss} → ∞ (Uniq (♭ xss)) → Uniq (later xss)
    later2 : ∀ {xs xss} → ∞ (Uniq (now (xs ∷ ♭ xss))) → Uniq (now (xs ∷ later xss))

  -- 隣接2要素の値が異なるリストならUniqを満たす(という証明ができる)
  test-Uniq-1 : Uniq (later (♯ (now ("a" ∷ later (♯ now ("b" ∷ now ("c" ∷ now [])))))))
  test-Uniq-1 = later1 (♯ later2 (♯ cons (λ ()) (cons (λ ()) singleton)))

  -- 隣接2要素の値に同じものがあるリストはUniqを満たせない(という証明は書けない)
  -- test-Uniq-2 : Uniq (later (♯ (now ("a" ∷ later (♯ now ("a" ∷ now ("c" ∷ now [])))))))
  -- test-Uniq-2 = later1 (♯ later2 (♯ cons {!ここが "a" ≢ "a" なので埋まらない!} (cons (λ ()) singleton)))

  -- 関数uniqの結果が性質Uniqを満たす
  uniq-is-Uniq : ∀ xss → Uniq (uniq xss)
  uniq-is-Uniq = go-is-Uniq nothing where
    -- goがUniqを満たすこと
    go-is-Uniq : ∀ mxs xss → Uniq (go mxs xss)
    go-is-Uniq mxs (now []) = nil
    go-is-Uniq mxs (now (xs ∷ now [])) with mxs ≟ just xs
    go-is-Uniq mxs (now (xs ∷ now [])) | yes p = nil
    go-is-Uniq mxs (now (xs ∷ now [])) | no ¬p = singleton
    go-is-Uniq mxs (now (xs ∷ now (ys ∷ yss))) with mxs ≟ just xs
    go-is-Uniq mxs (now (xs ∷ now (ys ∷ yss))) | yes p = go-is-Uniq mxs (now (ys ∷ yss))
    go-is-Uniq mxs (now (xs ∷ now (ys ∷ yss))) | no ¬p with just xs ≟ just ys
    go-is-Uniq mxs (now (xs ∷ now (ys ∷ yss))) | no ¬p | yes (just x≈y) rewrite x≈y = go-is-Uniq nothing (now (ys ∷ yss))
    go-is-Uniq mxs (now (xs ∷ now (ys ∷ yss))) | no ¬p₁ | no ¬p = cons (λ z → ¬p (just z)) (go-is-Uniq nothing (now (ys ∷ yss)))
    go-is-Uniq mxs (now (xs ∷ later xss)) with mxs ≟ just xs
    go-is-Uniq mxs (now (xs ∷ later xss)) | yes p = go-is-Uniq mxs (later xss)
    go-is-Uniq mxs (now (xs ∷ later xss)) | no ¬p = later2 (♯ go-is-Uniq nothing (now (xs ∷ ♭ xss)))
    go-is-Uniq mxs (later xss) = later1 (♯ go-is-Uniq mxs (♭ xss))

  -- 入力の部分列になっている性質 Subseq
  data Subseq : [ String ] → [ String ] → Set where
    nil : Subseq (now []) (now [])
    here : ∀ {xs xss ys yss} → xs ≡ ys → Subseq xss yss → Subseq (now (xs ∷ xss)) (now (ys ∷ yss))
    there : ∀ {xs xss yss} → Subseq xss yss → Subseq (now (xs ∷ xss)) yss
    laterₗ : ∀ {xss yss} → ∞ (Subseq (♭ xss) yss) → Subseq (later xss) yss
    laterᵣ : ∀ {xss yss} → ∞ (Subseq xss (♭ yss)) → Subseq xss (later yss)

  -- 関数uniqの結果が元の列に対しSubseqを満たす
  uniq-xss-is-Subseq-of-xss : ∀ xss → Subseq xss (uniq xss)
  uniq-xss-is-Subseq-of-xss = go-xss-is-Subseq-of-xss nothing where
    -- goがSubseqを満たすこと
    go-xss-is-Subseq-of-xss : ∀ mxs xss → Subseq xss (go mxs xss)
    go-xss-is-Subseq-of-xss mxs (now []) = nil
    go-xss-is-Subseq-of-xss mxs (now (xs ∷ now [])) with mxs ≟ just xs
    go-xss-is-Subseq-of-xss mxs (now (xs ∷ now [])) | yes p = there nil
    go-xss-is-Subseq-of-xss mxs (now (xs ∷ now [])) | no ¬p = here PropEq.refl nil
    go-xss-is-Subseq-of-xss mxs (now (xs ∷ now (ys ∷ yss))) with mxs ≟ just xs
    go-xss-is-Subseq-of-xss mxs (now (xs ∷ now (ys ∷ yss))) | yes p = there (go-xss-is-Subseq-of-xss mxs (now (ys ∷ yss)))
    go-xss-is-Subseq-of-xss mxs (now (xs ∷ now (ys ∷ yss))) | no ¬p = here PropEq.refl (go-xss-is-Subseq-of-xss (just xs) (now (ys ∷ yss)))
    go-xss-is-Subseq-of-xss mxs (now (xs ∷ later xss)) with mxs ≟ just xs
    go-xss-is-Subseq-of-xss mxs (now (xs ∷ later xss)) | yes p = there (laterₗ (♯ laterᵣ (♯ (go-xss-is-Subseq-of-xss mxs (♭ xss)))))
    go-xss-is-Subseq-of-xss mxs (now (xs ∷ later xss)) | no ¬p = here PropEq.refl (laterₗ (♯ laterᵣ (♯ (go-xss-is-Subseq-of-xss (just xs) (♭ xss)))))
    go-xss-is-Subseq-of-xss mxs (later x) = laterₗ (♯ laterᵣ (♯ go-xss-is-Subseq-of-xss mxs (♭ x)))

  as : [ String ]
  as = now ("a" ∷ later (♯ as))

  bs : [ String ]
  bs = now ("b" ∷ later (♯ bs))

  -- これがダメな(「ダメとしたい」)やつだけど弾けない，
  -- 無限である以上「いつか来るかもしれない」ため仕方ないのだがー
  bad-prop : Subseq as bs
  bad-prop = there (laterₗ (♯ bad-prop))
