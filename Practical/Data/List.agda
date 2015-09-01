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
module Practical.Data.List where

open import Function
open import Coinduction
open import Category.Monad
open import Category.Monad.Partiality hiding (map)

-- Colist に _⊥ の later相当を追加したもの
data [_] {a} (A : Set a) : Set a where
  []    : [ A ]
  _∷_   : (x : A) (xs : ∞ [ A ]) → [ A ]
  later : (x : ∞ [ A ]) → [ A ]

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → [ A ] → [ A ] → [ A ]
[]       ++ ys = []
x ∷ xs   ++ ys = x ∷ ♯ (♭ xs ++ ys)
later xs ++ ys = later (♯ (♭ xs ++ ys))

-- laterを持ってる型ならばstep(=run⊥)で⊥を取り込める という一般化をしたい？が…
step : ∀ {a} {A : Set a} → [ A ] ⊥ → [ A ]
step (now x)   = x
step (later x) = later (♯ step(♭ x))

zipWith : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          → (A → B → C) → [ A ] → [ B ] → [ C ]
zipWith f []         _          = []
zipWith f _          []         = []
zipWith f (later xs) ys         = later (♯ (zipWith f (♭ xs) ys))
zipWith f xs         (later ys) = later (♯ (zipWith f xs (♭ ys)))
zipWith f (x ∷ xs)   (y ∷ ys)   = f x y ∷ ♯ zipWith f (♭ xs) (♭ ys)

module WithProduct where
  open import Data.Product hiding (zip)

  -- 「later : (x : ∞ A) → A を構成子に持っている型A」みたいなのが取り出せる必要がある
  foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B ⊥ → B ⊥) → B ⊥ → [ A ] → B ⊥
  foldr c = go c (id , c) where
    go : ∀ {a b} {A : Set a} {B : Set b} → (A → B ⊥ → B ⊥) → ((B ⊥ → B ⊥) × (A → B ⊥ → B ⊥)) → B ⊥ → [ A ] → B ⊥
    go c (proj₁ , proj₂) n []       = proj₁ n
    go c (proj₁ , proj₂) n (x ∷ xs) = later (♯ go c ((proj₂ x) , (λ y → proj₂ x ∘ c y)) n (♭ xs))
    go c p n (later x)              = later (♯ (go c p n (♭ x)))

  zip : ∀ {a b} {A : Set a} {B : Set b} → [ A ] → [ B ] → [ A × B ]
  zip = zipWith (_,_)

open WithProduct public

foldl : ∀ {a b} {A : Set a} {B : Set b} → (A ⊥ → B → A ⊥) → A ⊥ → [ B ] → A ⊥
foldl c n []         = n
foldl c n (x ∷ xs)   = later (♯ foldl c (c n x) (♭ xs))
foldl c n (later xs) = later (♯ foldl c n (♭ xs))

concat : ∀ {a} {A : Set a} → [ [ A ] ] → [ A ]
concat []               = []
concat ([] ∷ xss)       = later (♯ concat (♭ xss))
concat ((x ∷ xs) ∷ xss) = x    ∷ ♯ concat (♭ xs ∷ xss)
concat (later xs ∷ xss) = later (♯ concat (♭ xs ∷ xss))
concat (later xss)      = later (♯ concat (♭ xss))

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → [ A ] → [ B ]
map f []         = []
map f (x ∷ xs)   = f x ∷ ♯ map f (♭ xs)
map f (later xs) = later (♯ map f (♭ xs))

concatMap : ∀ {a b} {A : Set a} {B : Set b} → (A → [ B ]) → [ A ] → [ B ]
concatMap f = concat ∘ map f

module WithBool where
  open import Data.Bool using (Bool; true; false)

  null : ∀ {a} {A : Set a} → [ A ] → Bool ⊥
  null []         = now true
  null (_ ∷ _)    = now false
  null (later xs) = later (♯ null (♭ xs))

  filter : ∀ {a} {A : Set a} → (A → Bool) → [ A ] → [ A ]
  filter p []         = []
  filter p (x ∷ xs) with p x
  ... | true          = x   ∷  ♯ filter p (♭ xs)
  ... | false         = later (♯ filter p (♭ xs))
  filter p (later xs) = later (♯ filter p (♭ xs))

open WithBool public

module WithConat where
  open import Data.Conat

  length : ∀ {a} {A : Set a} → [ A ] → Coℕ ⊥
  length = foldr (λ a b → suc ∘ ♯_ <$> b) (now zero) where
    open RawMonad (Category.Monad.Partiality.monad) using (_<$>_)

  replicate : ∀ {a} {A : Set a} → Coℕ → A → [ A ]
  replicate zero    x = []
  replicate (suc n) x = x ∷ ♯ replicate (♭ n) x

  repeat : ∀ {a} {A : Set a} → A → [ A ]
  repeat = replicate ∞ℕ

open WithConat public

module WithList where
  open import Data.List using (List; []; _∷_; _∷ʳ_)

  fromList : ∀ {a} {A : Set a} → List A → [ A ]
  fromList []       = []
  fromList (x ∷ xs) = x ∷ ♯ fromList xs

  toList : ∀ {a} {A : Set a} → [ A ] → List A ⊥
  toList = foldr (λ a b → (_∷_ a) <$> b) (now []) where
    open RawMonad (Category.Monad.Partiality.monad) using (_<$>_)

  reverse : ∀ {a} {A : Set a} → [ A ] → List A ⊥
  reverse xs = Data.List.reverse <$> toList xs where
    open RawMonad (Category.Monad.Partiality.monad) using (_<$>_)

  open import Data.Nat

  take : ∀ {a} {A : Set a} → ℕ → [ A ] → List A ⊥
  take = go [] where
    go : ∀ {a} {A : Set a} → List A → ℕ → [ A ] → List A ⊥
    go acc zero    xs         = now acc
    go acc (suc n) []         = now acc
    go acc (suc n) (x ∷ xs)   = later (♯ go (acc ∷ʳ x) n (♭ xs))
    go acc (suc n) (later xs) = later (♯ (go acc (suc n) (♭ xs)))

  drop : ∀ {a} {A : Set a} → ℕ → [ A ] → [ A ]
  drop zero    xs         = xs
  drop (suc n) []         = []
  drop (suc n) (x ∷ xs)   = later (♯ (drop n (♭ xs)))
  drop (suc n) (later xs) = later (♯ (drop (suc n) (♭ xs)))

  open import Data.Bool

  takeWhile : ∀ {a} {A : Set a} → (A → Bool) → [ A ] → [ A ]
  takeWhile p [] = []
  takeWhile p (x ∷ xs) with p x
  takeWhile p (x ∷ xs) | true  = x ∷ (♯ (takeWhile p (♭ xs)))
  takeWhile p (x ∷ xs) | false = []
  takeWhile p (later x) = later (♯ takeWhile p (♭ x))

  dropWhile : ∀ {a} {A : Set a} → (A → Bool) → [ A ] → [ A ]
  dropWhile p [] = []
  dropWhile p (x ∷ xs) with p x
  dropWhile p (x ∷ xs) | true  = later (♯ (dropWhile p (♭ xs)))
  dropWhile p (x ∷ xs) | false = []
  dropWhile p (later x) = later (♯ dropWhile p (♭ x))

open WithList public

module WithColist where
  open import Data.Colist using (Colist; []; _∷_)

  fromColist : ∀ {a} {A : Set a} → Colist A → [ A ]
  fromColist []       = []
  fromColist (x ∷ xs) = x ∷ ♯ fromColist (♭ xs)

  toColist : ∀ {a} {A : Set a} → [ A ] → Colist A ⊥
  toColist = foldr (λ a b → (_∷_ a) ∘ ♯_ <$> b) (now []) where
    open RawMonad (Category.Monad.Partiality.monad) using (_<$>_)

open WithColist public

intersperse : ∀ {a} {A : Set a} → A → [ A ] → [ A ]
intersperse a []         = []
intersperse a (x ∷ xs)   = x ∷ ♯ go a (♭ xs) where
  go : ∀ {a} {A : Set a} → A → [ A ] → [ A ]
  go b []         = []
  go b (y ∷ ys)   = b ∷ ♯ (y ∷ ♯ (go b (♭ ys)))
  go b (later ys) = later (♯ go b (♭ ys))
intersperse a (later xs) = later (♯ intersperse a (♭ xs))

module WithMaybe where
  open import Data.Maybe
  open import Data.Product

  unfoldr : ∀ {a b} {A : Set a} {B : Set b} → (B → Maybe (A × B)) → B → [ A ]
  unfoldr f b with f b
  ... | just (a' , b') = a' ∷ ♯ unfoldr f b'
  ... | nothing        = []

  iterate : ∀ {a} {A : Set a} → (A → A) → A → [ A ]
  iterate f = unfoldr (λ b → just (b , f b))

open WithMaybe public

module WithIO where
  open import IO using (IO; return; _>>=_)

  sequence : ∀ {a} {A : Set a} → [ IO A ] → IO [ A ]
  sequence []         = return []
  sequence (c ∷ cs)   = ♯ c                  >>= λ x  →
                        ♯ (♯ sequence (♭ cs) >>= λ xs →
                        ♯ return (x ∷ ♯ xs))
  sequence (later cs) = ♯ sequence (♭ cs) >>= λ xs →
                        ♯ return (later (♯ xs))

  mapM : ∀ {a b} {A : Set a} {B : Set b} →
         (A → IO B) → [ A ] → IO [ B ]
  mapM f = sequence ∘ map f

open WithIO public

-- 再帰，停止性: ドメインの値が小さくなっていかねばならない ←→ コドメインの値の構造が大きくなっていかねばならない
-- (laterで包まない)neverによる任意命題の構成を防ぐ
-- 結果の構造が大きくなる=コンストラクタが付く なので 型(命題)が確定する，また，分解がすぐ終わる

-- Coinductive Data は構造的に「小さくしていく変換ができない」 → filterの例
-- 実質的には皺を寄せるようにデータを集めることになる
-- Inductive Data は「インタラクティブな挙動の実現に向かない」
-- > つらみ! <
