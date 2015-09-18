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

shrink : Maybe String → [ String ] → [ String ]
shrink prev (now []) = now []
shrink prev (now (xs ∷ xss)) with prev ≟ just xs
... | yes _ = shrink prev xss
... | no  _ = now (xs ∷ shrink (just xs) xss)
shrink prev (later xs) = later (♯ shrink prev (♭ xs))

uniq : [ String ] → [ String ]
uniq = shrink nothing

main = run (interact (unlines ∘ map (fromList ∘ toList ∘ coloring) ∘ uniq ∘ lines)) where
  coloring : String → String
  coloring ss = "\x1b[32m" ++ ss ++ "\x1b[39m" -- わかりやすいように出力に色付け

-- uniqの性質を証明してみよう
module Properties where

  import Relation.Binary.PropositionalEquality as PropEq
  open PropEq using (_≡_; refl; _≢_; cong)
  module E = Equality {A = [ String ]'} (_≡_)

  -- xss が空リストに評価される値ならば，shrink prev xssも空リストに評価される
  shrink[]-is-[] : ∀ prev xss → xss E.⇓ [] → shrink prev xss E.⇓ []
  shrink[]-is-[] prev ._ (Equality.now x∼y) rewrite x∼y = Equality.now PropEq.refl
  shrink[]-is-[] prev ._ (Equality.laterˡ {x = x} x₁) = Equality.laterˡ (shrink[]-is-[] prev (♭ x) x₁)

  -- xss が空リストに評価される値ならば，uniq xssも空リストに評価される
  uniq[]-is-[] : ∀ xss → xss E.⇓ [] → uniq xss E.⇓ []
  uniq[]-is-[] = shrink[]-is-[] nothing

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
  uniq-is-Uniq = shrink-is-Uniq nothing where
    -- shrinkがUniqを満たすこと
    shrink-is-Uniq : ∀ prev xss → Uniq (shrink prev xss)
    shrink-is-Uniq prev (now []) = nil
    shrink-is-Uniq prev (now (xs ∷ now [])) with prev ≟ just xs
    shrink-is-Uniq prev (now (xs ∷ now [])) | yes p = nil
    shrink-is-Uniq prev (now (xs ∷ now [])) | no ¬p = singleton
    shrink-is-Uniq prev (now (xs ∷ now (ys ∷ yss))) with prev ≟ just xs
    shrink-is-Uniq prev (now (xs ∷ now (ys ∷ yss))) | yes p = shrink-is-Uniq prev (now (ys ∷ yss))
    shrink-is-Uniq prev (now (xs ∷ now (ys ∷ yss))) | no ¬p with just xs ≟ just ys
    shrink-is-Uniq prev (now (xs ∷ now (ys ∷ yss))) | no ¬p | yes (just x≈y) rewrite x≈y = shrink-is-Uniq nothing (now (ys ∷ yss))
    shrink-is-Uniq prev (now (xs ∷ now (ys ∷ yss))) | no ¬p₁ | no ¬p = cons (λ z → ¬p (just z)) (shrink-is-Uniq nothing (now (ys ∷ yss)))
    shrink-is-Uniq prev (now (xs ∷ later xss)) with prev ≟ just xs
    shrink-is-Uniq prev (now (xs ∷ later xss)) | yes p = shrink-is-Uniq prev (later xss)
    shrink-is-Uniq prev (now (xs ∷ later xss)) | no ¬p = later2 (♯ shrink-is-Uniq nothing (now (xs ∷ ♭ xss)))
    shrink-is-Uniq prev (later xss) = later1 (♯ shrink-is-Uniq prev (♭ xss))

  module BadDefinition where

    -- 入力の部分列になっている性質 Subseq (ただし，この定義には問題がある．後述)
    data Subseq : [ String ] → [ String ] → Set where
      nil : Subseq (now []) (now [])
      here : ∀ {xs xss yss} → Subseq xss yss → Subseq (now (xs ∷ xss)) (now (xs ∷ yss))
      there : ∀ {xs xss yss} → Subseq xss yss → Subseq (now (xs ∷ xss)) yss
      laterₗ : ∀ {xss yss} → ∞ (Subseq (♭ xss) yss) → Subseq (later xss) yss
      laterᵣ : ∀ {xss yss} → ∞ (Subseq xss (♭ yss)) → Subseq xss (later yss)

    -- 関数uniqの結果が元の列に対しSubseqを満たす
    uniq-xss-is-Subseq-of-xss : ∀ xss → Subseq xss (uniq xss)
    uniq-xss-is-Subseq-of-xss = shrink-xss-is-Subseq-of-xss nothing where
      -- shrinkがSubseqを満たすこと
      shrink-xss-is-Subseq-of-xss : ∀ prev xss → Subseq xss (shrink prev xss)
      shrink-xss-is-Subseq-of-xss prev (now []) = nil
      shrink-xss-is-Subseq-of-xss prev (now (xs ∷ now [])) with prev ≟ just xs
      shrink-xss-is-Subseq-of-xss prev (now (xs ∷ now [])) | yes p = there nil
      shrink-xss-is-Subseq-of-xss prev (now (xs ∷ now [])) | no ¬p = here nil
      shrink-xss-is-Subseq-of-xss prev (now (xs ∷ now (ys ∷ yss))) with prev ≟ just xs
      shrink-xss-is-Subseq-of-xss prev (now (xs ∷ now (ys ∷ yss))) | yes p = there (shrink-xss-is-Subseq-of-xss prev (now (ys ∷ yss)))
      shrink-xss-is-Subseq-of-xss prev (now (xs ∷ now (ys ∷ yss))) | no ¬p = here (shrink-xss-is-Subseq-of-xss (just xs) (now (ys ∷ yss)))
      shrink-xss-is-Subseq-of-xss prev (now (xs ∷ later xss)) with prev ≟ just xs
      shrink-xss-is-Subseq-of-xss prev (now (xs ∷ later xss)) | yes p = there (laterₗ (♯ laterᵣ (♯ (shrink-xss-is-Subseq-of-xss prev (♭ xss)))))
      shrink-xss-is-Subseq-of-xss prev (now (xs ∷ later xss)) | no ¬p = here (laterₗ (♯ laterᵣ (♯ (shrink-xss-is-Subseq-of-xss (just xs) (♭ xss)))))
      shrink-xss-is-Subseq-of-xss prev (later x) = laterₗ (♯ laterᵣ (♯ shrink-xss-is-Subseq-of-xss prev (♭ x)))

    as : [ String ]
    as = now ("a" ∷ later (♯ as))

    bs : [ String ]
    bs = now ("b" ∷ later (♯ bs))

    -- これがダメな(「ダメとしたい」)やつだけど弾けない，
    -- 無限である以上「いつか来るかもしれない」ため仕方ないのだがー
    bad-prop : Subseq as bs
    bad-prop = there (laterₗ (♯ bad-prop))
    -- どうにかするならData.Colist.Finiteみたいな性質を[_]にも定義し，
    -- Subseqを定めるための前提条件にするとかになる．
    -- ただ出元がIOだとその性質は証明できないんだけどね．

  -- というかそもそもSubseqなら有限の場合のみでしか，
  -- その性質の意味が無いんだから，Finiteは仮定していい
  open import Data.Product
  open import Practical.Data.List.Properties

  -- 入力の部分列になっている性質 Subseq (later の停止前提版)
  data Subseq : ∀ {xss yss : [ String ]} → Finite xss → Finite yss → Set where
    nil : Subseq [] []
    here : ∀ {xs xss yss} {finxss : Finite xss} {finyss : Finite yss} →
           Subseq finxss finxss → Subseq (xs ∷ finxss) (xs ∷ finyss)
    there : ∀ {xs xss yss} {finxss : Finite xss} {finyss : Finite yss} →
           Subseq finxss finxss → Subseq (xs ∷ finxss) finyss
    laterₗ : ∀ {xss xss' xss⇓xss' finxss' yss} {finyss : Finite yss} →
             Subseq finxss' finyss → Subseq (later {xs = xss} (xss' , xss⇓xss' , finxss')) finyss
    laterᵣ : ∀ {xss yss yss' yss⇓yss' finyss'} {finxss : Finite xss} →
             Subseq finxss finyss' → Subseq finxss (later {xs = yss} (yss' , yss⇓yss' , finyss'))

  -- これは示せないはず(SubseqのlaterはCoinductiveじゃないのでxssの分解では証明が止まらないだろう)
  -- uniq-xss-is-Subseq-of-xss : ∀ xss → Subseq xss (uniq xss)
  -- uniq-xss-is-Subseq-of-xss = ?

  shrink-xss≈shrink-whnf-xss : ∀ prev xss yss → xss E.⇓ yss → shrink prev xss E.≈ shrink prev (now yss)
  shrink-xss≈shrink-whnf-xss prev .(now yss) yss (Equality.now PropEq.refl) = Equivalence.refl PropEq.refl where open Equivalence
  shrink-xss≈shrink-whnf-xss prev ._ yss (Equality.laterˡ {x = xss} e) = Equality.laterˡ (shrink-xss≈shrink-whnf-xss prev (♭ xss) yss e)

  -- 有限リストに対するshrink prevはWHNFを持つ
  shrink-finite-has-whnf : ∀ {xss} → (prev : Maybe String) → Finite xss → ∃ λ yss → shrink prev xss E.⇓ yss
  shrink-finite-has-whnf prev [] = [] , Equality.now PropEq.refl
  shrink-finite-has-whnf prev (x ∷ []) with prev ≟ just x
  shrink-finite-has-whnf prev (x ∷ []) | yes p = [] , Equality.now PropEq.refl
  shrink-finite-has-whnf prev (x ∷ []) | no ¬p = x ∷ now [] , Equality.now PropEq.refl
  shrink-finite-has-whnf prev (x ∷ (x₁ ∷ fin)) with prev ≟ just x
  shrink-finite-has-whnf prev (x ∷ (x₁ ∷ fin)) | yes p = shrink-finite-has-whnf prev (x₁ ∷ fin)
  shrink-finite-has-whnf prev (x ∷ (_∷_  x₁ {xss} fin)) | no ¬p = (x ∷ shrink (just x) (now (x₁ ∷ xss))) , Equality.now PropEq.refl
  shrink-finite-has-whnf prev (x ∷ later {xs} fin) with prev ≟ just x
  shrink-finite-has-whnf prev (x ∷ later {xs} fin) | yes p = shrink-finite-has-whnf prev (later fin)
  shrink-finite-has-whnf prev (x ∷ later {xs} fin) | no ¬p = x ∷ shrink (just x) (later xs) , Equality.now PropEq.refl
  shrink-finite-has-whnf prev (later {xs} (ys , finys , proj₃)) with shrink-finite-has-whnf prev proj₃
  ... | p = proj₁ p , Equivalence.trans PropEq.trans (shrink-xss≈shrink-whnf-xss prev (later xs) ys finys) (proj₂ p) where open Equivalence

  -- 有限リストに対するshrink prevは有限リスト
  shrink-finite-is-finite : ∀ {xss} → (prev : Maybe String) → Finite xss → Finite (shrink prev xss)
  shrink-finite-is-finite prev [] = []
  shrink-finite-is-finite prev (x ∷ []) with prev ≟ just x
  shrink-finite-is-finite prev (x ∷ []) | yes p = []
  shrink-finite-is-finite prev (x ∷ []) | no ¬p = x ∷ []
  shrink-finite-is-finite prev (x ∷ (x₁ ∷ fin)) with prev ≟ just x
  shrink-finite-is-finite prev (x ∷ (x₁ ∷ fin)) | yes p = shrink-finite-is-finite prev (x₁ ∷ fin)
  shrink-finite-is-finite prev (x ∷ (x₁ ∷ fin)) | no ¬p = x ∷ shrink-finite-is-finite (just x) (x₁ ∷ fin)
  shrink-finite-is-finite prev (x ∷ later fin) with prev ≟ just x
  shrink-finite-is-finite prev (x ∷ later fin) | yes p = shrink-finite-is-finite prev (later fin)
  shrink-finite-is-finite prev (x ∷ later fin) | no ¬p = x ∷ shrink-finite-is-finite (just x) (later fin)
  shrink-finite-is-finite prev (later {xs} (ys , xs⇓ys , finys)) = later (proj₁ whnf , Equivalence.trans PropEq.trans (shrink-xss≈shrink-whnf-xss prev (later xs) ys xs⇓ys) (proj₂ whnf) , lemma (shrink prev (now ys)) (proj₁ whnf) (proj₂ whnf) (shrink-finite-is-finite prev finys)) where
    open Equivalence
    open import Data.Unit
    whnf : ∃ λ zs → shrink prev (now ys) E.⇓ zs
    whnf = shrink-finite-has-whnf prev finys
    lemma : ∀ xs ys → xs E.⇓ ys → Finite xs → Finite (now ys)
    lemma .(now []) .[] (Equality.now PropEq.refl) [] = []
    lemma ._ ._ (Equality.now PropEq.refl) (x ∷ fin) = x ∷ fin
    lemma ._ ys₁ xs⇓ys₁ (later (proj₁ , proj₂ , proj₃)) = lemma (now proj₁) ys₁ (Equivalence.trans PropEq.trans (Equivalence.sym sym-≡ tt proj₂) xs⇓ys₁) proj₃ where
      sym-≡ : Symmetric _≡_
      sym-≡ PropEq.refl = PropEq.refl

  -- 有限リストに対するuniqも有限リスト
  uniq-finite-is-finite : ∀ {xss} → Finite xss → Finite (uniq xss)
  uniq-finite-is-finite = shrink-finite-is-finite nothing

  Subseq-refl : ∀ {xss} → (finxss : Finite xss) → Subseq finxss finxss
  Subseq-refl [] = nil
  Subseq-refl (x ∷ finxss) = here (Subseq-refl finxss)
  Subseq-refl (later (proj₁ , proj₂ , proj₃)) = laterₗ (laterᵣ (Subseq-refl proj₃))
{-
  shrink-xss-is-Subseq-of-xss : ∀ {xss} → (prev : Maybe String) → (finxss : Finite xss) →
                                Subseq finxss (shrink-finite-is-finite prev finxss)
  shrink-xss-is-Subseq-of-xss prev [] = nil
  shrink-xss-is-Subseq-of-xss prev (x ∷ []) with prev ≟ just x
  shrink-xss-is-Subseq-of-xss prev (x ∷ []) | yes p = there nil
  shrink-xss-is-Subseq-of-xss prev (x ∷ []) | no ¬p = here nil
  shrink-xss-is-Subseq-of-xss prev (x ∷ (x₁ ∷ finxss)) with prev ≟ just x
  shrink-xss-is-Subseq-of-xss prev (x ∷ (x₁ ∷ finxss)) | yes p = there (here (Subseq-refl finxss))
  shrink-xss-is-Subseq-of-xss prev (x ∷ (x₁ ∷ finxss)) | no ¬p = here (here (Subseq-refl finxss))
  shrink-xss-is-Subseq-of-xss prev (x ∷ later fin) with prev ≟ just x
  shrink-xss-is-Subseq-of-xss prev (x ∷ later fin) | yes p = there (Subseq-refl (later fin))
  shrink-xss-is-Subseq-of-xss prev (x ∷ later fin) | no ¬p = here (Subseq-refl (later fin))
  shrink-xss-is-Subseq-of-xss prev (later {xs} (ys , xs⇓ys , finys)) = laterₗ {!!}

  -- xssがFiniteならばSubseqも示せる(はず)
  uniq-xss-is-Subseq-of-xss : ∀ {xss} → (finxss : Finite xss) → Subseq finxss (uniq-finite-is-finite finxss)
  uniq-xss-is-Subseq-of-xss = shrink-xss-is-Subseq-of-xss nothing
-}
