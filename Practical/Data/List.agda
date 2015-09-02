-- 実はHaskellのリスト相当を考えると，
-- 実用上の停止性まで考慮するとListそのままでもColistそのままでもなく，
-- 以下のような何かを使っておいたほうが記述は簡単
--
-- List A はstrictすぎる，Colist Aには隙間が足りない
-- Colist A ⊥ は隙間が前にしか入れられない
--
-- Listだけじゃない，Haskellライクに書こうとすると，
-- 「laterを持っていること」はあらゆる型に対して要請されてくる
-- また，そういう構成子laterを持っているという性質を
-- クラスのように扱えなければならない
--
-- どこで使うかによっても何が現れるかが違う．具体的には
-- filter では [ A ] → [ A ] だけど，
-- nubBy  だと [ A ] → List A ⊥ でいい
-- list of list 等だと，どこにlaterを吸収させるかで性質が変わるかも
--
module Practical.Data.List where

open import Function
open import Coinduction
open import Category.Monad
open import Category.Monad.Partiality hiding (map; monad)

-- List の cdr に _⊥ を挟んだもの
mutual
  data [_]' {a} (A : Set a) : Set a where
    []    : [ A ]'
    _∷_   : (x : A) (xs : [ A ]) → [ A ]'

  [_] : ∀ {a} → Set a → Set a
  [ A ] = [ A ]' ⊥

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → [ A ] → [ A ] → [ A ]
now []       ++ ys = ys
now (x ∷ xs) ++ ys = now (x ∷ (xs ++ ys))
later xs     ++ ys = later (♯ (♭ xs ++ ys))

zipWith : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A → B → C) → [ A ] → [ B ] → [ C ]
zipWith f (now [])       _              = now []
zipWith f _              (now [])       = now []
zipWith f (later xs)     ys             = later (♯ zipWith f (♭ xs) ys)
zipWith f xs             (later ys)     = later (♯ zipWith f xs (♭ ys))
zipWith f (now (x ∷ xs)) (now (y ∷ ys)) = now (f x y ∷ zipWith f xs ys)

module WithProduct where
  open import Data.Product hiding (zip)

  -- 「later : (x : ∞ A) → A を構成子に持っている型A」みたいなのが取り出せる必要がある
  -- なんかこのfoldrはクッソダメな気がするが停止性ががが
  foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B ⊥ → B ⊥) → B ⊥ → [ A ] → B ⊥
  foldr c = go c (id , c) where
    go : ∀ {a b} {A : Set a} {B : Set b} → (A → B ⊥ → B ⊥) → ((B ⊥ → B ⊥) × (A → B ⊥ → B ⊥)) → B ⊥ → [ A ] → B ⊥
    go c (proj₁ , proj₂) n (now [])       = proj₁ n
    go c (proj₁ , proj₂) n (now (x ∷ xs)) = go c ((proj₂ x) , (λ y → proj₂ x ∘ c y)) n xs
    go c p n (later x)                    = later (♯ (go c p n (♭ x)))

  zip : ∀ {a b} {A : Set a} {B : Set b} → [ A ] → [ B ] → [ A × B ]
  zip = zipWith (_,_)

open WithProduct public

foldl : ∀ {a b} {A : Set a} {B : Set b} → (A ⊥ → B → A ⊥) → A ⊥ → [ B ] → A ⊥
foldl c n (now [])       = n
foldl c n (now (x ∷ xs)) = foldl c (c n x) xs
foldl c n (later xs)     = later (♯ foldl c n (♭ xs))

concat : ∀ {a} {A : Set a} → [ [ A ] ] → [ A ]
concat (now [])                   = now []
concat (now (now [] ∷ xss))       = concat xss
concat (now (now (x ∷ xs) ∷ xss)) = now (x ∷ concat (now (xs ∷ xss)))
concat (now (later xs ∷ xss))     = later (♯ (concat (now (♭ xs ∷ xss))))
concat (later xss)                = later (♯ concat (♭ xss))

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → [ A ] → [ B ]
map f (now [])       = now []
map f (now (x ∷ xs)) = now (f x ∷ map f xs)
map f (later xs)     = later (♯ map f (♭ xs))

concatMap : ∀ {a b} {A : Set a} {B : Set b} → (A → [ B ]) → [ A ] → [ B ]
concatMap f = concat ∘ map f

monad : ∀ {a} → RawMonad {a} [_]
monad = record
  { return = λ x → now (x ∷ now [])
  ; _>>=_ = λ xs f → concatMap f xs
  }

monadZero : ∀ {a} → RawMonadZero {a} [_]
monadZero = record
  { monad = monad
  ; ∅     = now []
  }

monadPlus : ∀ {a} → RawMonadPlus {a} [_]
monadPlus = record
  { monadZero = monadZero
  ; _∣_       = _++_
  }

module WithBool where
  open import Data.Bool using (Bool; true; false)

  null : ∀ {a} {A : Set a} → [ A ] → Bool ⊥
  null (now [])      = now true
  null (now (_ ∷ _)) = now false
  null (later xs)    = later (♯ null (♭ xs))

  filter : ∀ {a} {A : Set a} → (A → Bool) → [ A ] → [ A ]
  filter p (now [])         = now []
  filter p (now (x ∷ xs)) with p x
  ... | true                = now (x ∷ filter p xs)
  ... | false               = later (♯ filter p xs)
  filter p (later xs)       = later (♯ filter p (♭ xs))

  any : ∀ {a} {A : Set a} → (A → Bool) → [ A ] → Bool ⊥
  any p (now [])   = now false
  any p (now (x ∷ xs)) with p x
  ... | true       = now true
  ... | false      = later (♯ any p xs)
  any p (later xs) = later (♯ any p (♭ xs))

  all : ∀ {a} {A : Set a} → (A → Bool) → [ A ] → Bool ⊥
  all p (now [])   = now true
  all p (now (x ∷ xs)) with p x
  ... | true       = later (♯ any p xs)
  ... | false      = now false
  all p (later xs) = later (♯ any p (♭ xs))

  open import Data.Maybe

  listToMaybe : ∀ {a} {A : Set a} → [ A ] → Maybe A ⊥
  listToMaybe (now [])       = now nothing
  listToMaybe (now (x ∷ xs)) = now (just x)
  listToMaybe (later xs)     = later (♯ listToMaybe (♭ xs))

  find : ∀ {a} {A : Set a} → (A → Bool) → [ A ] → Maybe A ⊥
  find p = listToMaybe ∘ filter p

open WithBool public

module WithConat where
  open import Data.Conat

  length : ∀ {a} {A : Set a} → [ A ] → Coℕ ⊥
  length = foldr (λ a b → suc ∘ ♯_ <$> b) (now zero) where
    open RawMonad (Category.Monad.Partiality.monad) using (_<$>_)

  replicate : ∀ {a} {A : Set a} → Coℕ → A → [ A ]
  replicate zero    x = now []
  replicate (suc n) x = now (x ∷ later (♯ replicate (♭ n) x))

  repeat : ∀ {a} {A : Set a} → A → [ A ]
  repeat = replicate ∞ℕ

open WithConat public

module WithList where
  open import Data.List using (List; []; _∷_; _∷ʳ_)

  fromList : ∀ {a} {A : Set a} → List A → [ A ]
  fromList []       = now []
  fromList (x ∷ xs) = now (x ∷ fromList xs)

  toList : ∀ {a} {A : Set a} → [ A ] → List A ⊥
  toList = go [] where
    go : ∀ {a} {A : Set a} → List A → [ A ] → List A ⊥
    go acc (now [])       = now acc
    go acc (now (x ∷ xs)) = go (acc ∷ʳ x) xs
    go acc (later x)      = later (♯ go acc (♭ x))

  reverse : ∀ {a} {A : Set a} → [ A ] → List A ⊥
  reverse xs = Data.List.reverse <$> toList xs where
    open RawMonad (Category.Monad.Partiality.monad) using (_<$>_)

  open import Data.Nat

  take : ∀ {a} {A : Set a} → ℕ → [ A ] → List A ⊥
  take = go [] where
    go : ∀ {a} {A : Set a} → List A → ℕ → [ A ] → List A ⊥
    go acc zero    xs             = now acc
    go acc (suc n) (now [])       = now acc
    go acc (suc n) (now (x ∷ xs)) = go (acc ∷ʳ x) n xs
    go acc (suc n) (later xs)     = later (♯ (go acc (suc n) (♭ xs)))

  drop : ∀ {a} {A : Set a} → ℕ → [ A ] → [ A ]
  drop zero    xs             = xs
  drop (suc n) (now [])       = now []
  drop (suc n) (now (x ∷ xs)) = drop n xs
  drop (suc n) (later xs)     = later (♯ drop (suc n) (♭ xs))

  open import Data.Bool

  takeWhile : ∀ {a} {A : Set a} → (A → Bool) → [ A ] → [ A ]
  takeWhile p (now [])  = now []
  takeWhile p (now (x ∷ xs)) with p x
  ... | true            = now (x ∷ takeWhile p xs)
  ... | false           = now []
  takeWhile p (later x) = later (♯ takeWhile p (♭ x))

  dropWhile : ∀ {a} {A : Set a} → (A → Bool) → [ A ] → [ A ]
  dropWhile p (now [])  = now []
  dropWhile p (now (x ∷ xs)) with p x
  ... | true            = dropWhile p xs
  ... | false           = now []
  dropWhile p (later x) = later (♯ dropWhile p (♭ x))

open WithList public

module WithColist where
  open import Data.Colist using (Colist; []; _∷_)

  fromColist : ∀ {a} {A : Set a} → Colist A → [ A ]
  fromColist []       = now []
  fromColist (x ∷ xs) = now (x ∷ later (♯ fromColist (♭ xs)))

  toColist : ∀ {a} {A : Set a} → [ A ] → Colist A ⊥
  toColist = foldr (λ a b → (_∷_ a) ∘ ♯_ <$> b) (now []) where
    open RawMonad (Category.Monad.Partiality.monad) using (_<$>_)

open WithColist public

intersperse : ∀ {a} {A : Set a} → A → [ A ] → [ A ]
intersperse a (now [])       = now []
intersperse a (now (x ∷ xs)) = now (x ∷ go a xs) where
  go : ∀ {a} {A : Set a} → A → [ A ] → [ A ]
  go b (now [])       = now []
  go b (now (y ∷ ys)) = now (b ∷ now (y ∷ go b ys))
  go b (later ys)     = later (♯ go b (♭ ys))
intersperse a (later xs)     = later (♯ intersperse a (♭ xs))

module WithMaybe where
  open import Data.Maybe
  open import Data.Product

  unfoldr : ∀ {a b} {A : Set a} {B : Set b} → (B → Maybe (A × B)) → B → [ A ]
  unfoldr f b with f b
  ... | just (a' , b') = now (a' ∷ later (♯ unfoldr f b'))
  ... | nothing        = now []

  iterate : ∀ {a} {A : Set a} → (A → A) → A → [ A ]
  iterate f = unfoldr (λ b → just (b , f b))

open WithMaybe public

module WithIO where
  open import IO using (IO; return; _>>=_)

  sequence : ∀ {a} {A : Set a} → [ IO A ] → IO [ A ]
  sequence (now [])       = return (now [])
  sequence (now (c ∷ cs)) = ♯ c              >>= λ x  →
                            ♯ (♯ sequence cs >>= λ xs →
                            ♯ return (now (x ∷ xs)))
  sequence (later cs)     = ♯ sequence (♭ cs) >>= λ xs →
                            ♯ return (later (♯ xs))

  mapM : ∀ {a b} {A : Set a} {B : Set b} → (A → IO B) → [ A ] → IO [ B ]
  mapM f = sequence ∘ map f

open WithIO public

-- 再帰，停止性: ドメインの値が小さくなっていかねばならない ←→ コドメインの値の構造が大きくなっていかねばならない
-- (laterで包まない)neverによる任意命題の構成を防ぐ
-- 結果の構造が大きくなる=コンストラクタが付く なので 型(命題)が確定する，また，分解がすぐ終わる

-- Coinductive Data は構造的に「小さくしていく変換ができない」 → filterの例
-- 実質的には皺を寄せるようにデータを集めることになる
-- Inductive Data は「インタラクティブな挙動の実現に向かない」
-- > つらみ! <
