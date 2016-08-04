module Practical.System.IO where

open import Function
open import Coinduction
import IO as StdIO
open StdIO using (IO; _>>=_; return)
open import Practical.Data.String
open import Practical.Data.List
open import Data.Unit using (⊤; tt)
open import Data.Char using (Char)
import Data.String as StdStr
import Data.List as StdList

void : ∀ {a} → IO a → IO ⊤
void action = ♯ action >>= λ _ → ♯ return tt

putChar : Char → IO ⊤
putChar = StdIO.putStr ∘ StdStr.fromList ∘ StdList.[_]

putStr : String → IO ⊤
putStr = void ∘ mapM putChar

putStrLn : String → IO ⊤
putStrLn str = void (♯ putStr str >>= λ _ → ♯ putChar '\n')

getContents : IO String
getContents = ♯ StdIO.getContents >>= λ x → ♯ (return ∘ fromColist $ x)

interact : (String → String) → IO ⊤
interact f = ♯ StdIO.getContents >>= λ x → ♯ (void ∘ mapM putChar ∘ f ∘ fromColist $ x) where
  open import Function
  open import Data.List using ([_])
  open import Data.String using (fromList)

-- インタラクティブプログラムの記述パターンのひとつ
-- 1. I/O(入力) を取り出す
-- 2. 大概 Coinductive なので Partiality Monad (もしくはそれに準ずる構造) で，必要な Inductive に巻き取る
-- 3. Inductice (必要なら Coinductive) 上で処理や証明を書く
-- 4. 結果をI/O(出力)しながら巻き取り時のゴミ(laterコンストラクタ)を消化(return tt)する
