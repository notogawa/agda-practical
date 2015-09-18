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
  module E = Equality {A = [ String ]'} (_≡_)

  -- xss が空リストに評価される値ならば，uniq xssも空リストに評価される
  uniq[]-is-[] : ∀ xss → xss E.⇓ [] → uniq xss E.⇓ []
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

  -- 入力の部分列になっている性質 BadSubseq (ただし，この定義には問題がある．後述)
  data BadSubseq : [ String ] → [ String ] → Set where
    nil : BadSubseq (now []) (now [])
    here : ∀ {xs xss yss} → BadSubseq xss yss → BadSubseq (now (xs ∷ xss)) (now (xs ∷ yss))
    there : ∀ {xs xss yss} → BadSubseq xss yss → BadSubseq (now (xs ∷ xss)) yss
    laterₗ : ∀ {xss yss} → ∞ (BadSubseq (♭ xss) yss) → BadSubseq (later xss) yss
    laterᵣ : ∀ {xss yss} → ∞ (BadSubseq xss (♭ yss)) → BadSubseq xss (later yss)

  -- 関数uniqの結果が元の列に対しBadSubseqを満たす
  uniq-xss-is-BadSubseq-of-xss : ∀ xss → BadSubseq xss (uniq xss)
  uniq-xss-is-BadSubseq-of-xss = go-xss-is-BadSubseq-of-xss nothing where
    -- goがBadSubseqを満たすこと
    go-xss-is-BadSubseq-of-xss : ∀ mxs xss → BadSubseq xss (go mxs xss)
    go-xss-is-BadSubseq-of-xss mxs (now []) = nil
    go-xss-is-BadSubseq-of-xss mxs (now (xs ∷ now [])) with mxs ≟ just xs
    go-xss-is-BadSubseq-of-xss mxs (now (xs ∷ now [])) | yes p = there nil
    go-xss-is-BadSubseq-of-xss mxs (now (xs ∷ now [])) | no ¬p = here nil
    go-xss-is-BadSubseq-of-xss mxs (now (xs ∷ now (ys ∷ yss))) with mxs ≟ just xs
    go-xss-is-BadSubseq-of-xss mxs (now (xs ∷ now (ys ∷ yss))) | yes p = there (go-xss-is-BadSubseq-of-xss mxs (now (ys ∷ yss)))
    go-xss-is-BadSubseq-of-xss mxs (now (xs ∷ now (ys ∷ yss))) | no ¬p = here (go-xss-is-BadSubseq-of-xss (just xs) (now (ys ∷ yss)))
    go-xss-is-BadSubseq-of-xss mxs (now (xs ∷ later xss)) with mxs ≟ just xs
    go-xss-is-BadSubseq-of-xss mxs (now (xs ∷ later xss)) | yes p = there (laterₗ (♯ laterᵣ (♯ (go-xss-is-BadSubseq-of-xss mxs (♭ xss)))))
    go-xss-is-BadSubseq-of-xss mxs (now (xs ∷ later xss)) | no ¬p = here (laterₗ (♯ laterᵣ (♯ (go-xss-is-BadSubseq-of-xss (just xs) (♭ xss)))))
    go-xss-is-BadSubseq-of-xss mxs (later x) = laterₗ (♯ laterᵣ (♯ go-xss-is-BadSubseq-of-xss mxs (♭ x)))

  as : [ String ]
  as = now ("a" ∷ later (♯ as))

  bs : [ String ]
  bs = now ("b" ∷ later (♯ bs))

  -- これがダメな(「ダメとしたい」)やつだけど弾けない，
  -- 無限である以上「いつか来るかもしれない」ため仕方ないのだがー
  bad-prop : BadSubseq as bs
  bad-prop = there (laterₗ (♯ bad-prop))
  -- どうにかするならData.Colist.Finiteみたいな性質を[_]にも定義し，
  -- BadSubseqを定めるための前提条件にするとかになる．
  -- ただ出元がIOだとその性質は証明できないんだけどね．

  -- というかそもそもSubseqなら有限の場合のみでしか，
  -- その性質の意味が無いんだから，Finiteは仮定していい
  open import Data.Product
  open import Practical.Data.List.Properties

  -- 入力の部分列になっている性質 Subseq (later の停止前提版)
  data Subseq : ∀ {xss yss : [ String ]} → Finite xss → Finite yss → Set where
    nil : Subseq [] []
    here : ∀ {xs xss yss} {finxss : Finite xss} {finyss : Finite yss} → Subseq finxss finxss → Subseq (xs ∷ finxss) (xs ∷ finyss)
    there : ∀ {xs xss yss} {finxss : Finite xss} {finyss : Finite yss} → Subseq finxss finxss → Subseq (xs ∷ finxss) finyss
--    laterₗ : ∀ {xss yss} → (∃ λ xss' → ♭ xss ⇓ xss' × Subseq xss' yss) → Subseq (later xss) yss
--    laterᵣ : ∀ {xss yss} → (∃ λ yss' → ♭ yss ⇓ yss' × Subseq xss yss') → Subseq xss (later yss)

  -- これは示せないはず(SubseqのlaterはCoinductiveじゃないのでxssの分解では証明が止まらないだろう)
  -- uniq-xss-is-Subseq-of-xss : ∀ xss → Subseq xss (uniq xss)
  -- uniq-xss-is-Subseq-of-xss = ?

  go[]-is-[] : ∀ mxs xss → xss E.⇓ [] → go mxs xss E.⇓ []
  go[]-is-[] mxs ._ (Equality.now x∼y) rewrite x∼y = Equality.now PropEq.refl
  go[]-is-[] mxs ._ (Equality.laterˡ {x = x} x₁) = Equality.laterˡ (go[]-is-[] mxs (♭ x) x₁)

  go-xss≈go-whnf-xss : ∀ mxs xss yss → xss E.⇓ yss → go mxs xss E.≈ go mxs (now yss)
  go-xss≈go-whnf-xss mxs .(now yss) yss (Equality.now PropEq.refl) = Equivalence.refl PropEq.refl where open Equivalence
  go-xss≈go-whnf-xss mxs ._ yss (Equality.laterˡ {x = xss} e) = Equality.laterˡ (go-xss≈go-whnf-xss mxs (♭ xss) yss e)

  finite-go-has-whnf : ∀ {xss} → (mxs : Maybe String) → Finite xss → ∃ λ yss → go mxs xss E.⇓ yss
  finite-go-has-whnf mxs [] = [] , Equality.now PropEq.refl
  finite-go-has-whnf mxs (x ∷ []) with mxs ≟ just x
  finite-go-has-whnf mxs (x ∷ []) | yes p = [] , Equality.now PropEq.refl
  finite-go-has-whnf mxs (x ∷ []) | no ¬p = x ∷ now [] , Equality.now PropEq.refl
  finite-go-has-whnf mxs (x ∷ (x₁ ∷ fin)) with mxs ≟ just x
  finite-go-has-whnf mxs (x ∷ (x₁ ∷ fin)) | yes p = finite-go-has-whnf mxs (x₁ ∷ fin)
  finite-go-has-whnf mxs (x ∷ (_∷_  x₁ {xss} fin)) | no ¬p = (x ∷ go (just x) (now (x₁ ∷ xss))) , Equality.now PropEq.refl
  finite-go-has-whnf mxs (x ∷ later {xs} fin) with mxs ≟ just x
  finite-go-has-whnf mxs (x ∷ later {xs} fin) | yes p = finite-go-has-whnf mxs (later fin)
  finite-go-has-whnf mxs (x ∷ later {xs} fin) | no ¬p = x ∷ go (just x) (later xs) , Equality.now PropEq.refl
  finite-go-has-whnf mxs (later {xs} (ys , finys , proj₃)) with finite-go-has-whnf mxs proj₃
  ... | p = proj₁ p , Equivalence.trans PropEq.trans (go-xss≈go-whnf-xss mxs (later xs) ys finys) (proj₂ p) where open Equivalence

  finite-uniq-has-whnf : ∀ {xss} → Finite xss → ∃ λ yss → uniq xss E.⇓ yss
  finite-uniq-has-whnf = finite-go-has-whnf nothing

  later-keep-Finite : ∀ {a} {A : Set a} {xss : [ A ]} → Finite xss → Finite (later (♯ xss))
  later-keep-Finite [] = later ([] , Equality.laterˡ (Equality.now PropEq.refl) , [])
  later-keep-Finite (_∷_ x {xs} fin) = later (x ∷ xs , Equality.laterˡ (Equality.now PropEq.refl) , x ∷ fin)
  later-keep-Finite (later (proj₁ , proj₂ , proj₃)) = later (proj₁ , Equality.laterˡ proj₂ , proj₃)

  later-keep-Finite' : ∀ {a} {A : Set a} {xss : [ A ]} → Finite (later (♯ xss)) → Finite xss
  later-keep-Finite' (later (.[] , Equality.laterˡ (Equality.now PropEq.refl) , [])) = []
  later-keep-Finite' (later (.[] , Equality.laterˡ (Equality.laterˡ proj₂) , [])) = later ([] , Equality.laterˡ proj₂ , [])
  later-keep-Finite' (later (._ , Equality.laterˡ (Equality.now PropEq.refl) , x ∷ proj₃)) = x ∷ proj₃
  later-keep-Finite' (later (._ , Equality.laterˡ (Equality.laterˡ proj₂) , _∷_ x {xs} proj₃)) = later (x ∷ xs , Equality.laterˡ proj₂ , x ∷ proj₃)

  go-finite-is-finite : ∀ {xss} → (mxs : Maybe String) → Finite xss → Finite (go mxs xss)
  go-finite-is-finite mxs [] = []
  go-finite-is-finite mxs (x ∷ []) with mxs ≟ just x
  go-finite-is-finite mxs (x ∷ []) | yes p = []
  go-finite-is-finite mxs (x ∷ []) | no ¬p = x ∷ []
  go-finite-is-finite mxs (x ∷ (x₁ ∷ fin)) with mxs ≟ just x
  go-finite-is-finite mxs (x ∷ (x₁ ∷ fin)) | yes p = go-finite-is-finite mxs (x₁ ∷ fin)
  go-finite-is-finite mxs (x ∷ (x₁ ∷ fin)) | no ¬p = x ∷ go-finite-is-finite (just x) (x₁ ∷ fin)
  go-finite-is-finite mxs (x ∷ later fin) with mxs ≟ just x
  go-finite-is-finite mxs (x ∷ later fin) | yes p = go-finite-is-finite mxs (later fin)
  go-finite-is-finite mxs (x ∷ later fin) | no ¬p = x ∷ go-finite-is-finite (just x) (later fin)
  go-finite-is-finite mxs (later {xs} (ys , xs⇓ys , finys)) = later (proj₁ yy , Equivalence.trans PropEq.trans xx (proj₂ yy) , lemma (go mxs (now ys)) (proj₁ yy) (proj₂ yy) yyy) where
    open Equivalence
    open import Data.Unit
    xx : go mxs (later xs) E.≈ go mxs (now ys)
    xx = go-xss≈go-whnf-xss mxs (later xs) ys xs⇓ys
    yy : ∃ λ zs → go mxs (now ys) E.⇓ zs
    yy = finite-go-has-whnf mxs finys
    yyy : Finite (go mxs (now ys))
    yyy = go-finite-is-finite mxs finys
    lemma : ∀ xs ys → xs E.⇓ ys → Finite xs → Finite (now ys)
    lemma .(now []) .[] (Equality.now PropEq.refl) [] = []
    lemma ._ ._ (Equality.now PropEq.refl) (x ∷ fin) = x ∷ fin
    lemma ._ ys₁ xs⇓ys₁ (later (proj₁ , proj₂ , proj₃)) = lemma (now proj₁) ys₁ (Equivalence.trans PropEq.trans (Equivalence.sym sm tt proj₂) xs⇓ys₁) proj₃ where
      sm : Symmetric _≡_
      sm PropEq.refl = PropEq.refl

  uniq-finite-is-finite : ∀ {xss} → Finite xss → Finite (uniq xss)
  uniq-finite-is-finite = go-finite-is-finite nothing
{-
  -- xssがFiniteならばSubseqも示せる(はず)
  uniq-xss-is-Subseq-of-xss : ∀ {xss} → (finxss : Finite xss) → Subseq finxss (uniq-finite-is-finite finxss)
  uniq-xss-is-Subseq-of-xss = {!!}
-}
