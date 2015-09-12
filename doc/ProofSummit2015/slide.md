% 実用Agda坂
% notogawa
% 2015/9/12

# "実用"

* for 証明士
    * 何らかの命題が証明できる
    * ある意味動くものができる必要は無い
* for プログラマ
    * 処理(関数)が定義できる
    * 定義した処理について何らかの性質が証明できる
    * 証明済みの処理が<strong style="color: #F00">そのまま動かせる</strong>

#
## 発表内容

ふたつの観点

1. 証明系としてのAgda
2. 言語としてのAgda

後者を重点

* Agdaでプログラミングし易いライブラリを作った
    * そこに至るまでの話
    * その上で証明も加えてみる

#
## 本日のお題

uniqコマンドを作ってみよう

~~~~
$ uniq
abcd <- 入力してEnter
abcd <- 出力される
abcd <- 入力してEnter
abcd <- 入力してEnter
abc  <- 入力してEnter
abc  <- 出力される
...
~~~~

Haskellでは

~~~~
main = interact (unlines . uniq . lines) where
  uniq = 以下略
~~~~

#
## Agda実行方法

* MAlonzoによるHaskellコード生成
    * Agdaで全て書く
        * main関数からIOもAgdaで書く
    * Agdaの関数をexportしHaskellから使う
        * Agda 2.4.0 以降
        * main等はHaskellで書く

* 詳細と比較は[去年の発表「本当はつらいReal World Agda」](https://github.com/notogawa/agda-haskell-example)を
* 今日は全てAgdaで書く

→ <strong style="color: #F00">停止性等に対する甘えが許されない</strong>

#
## Agdaプログラミング

* ライブラリを使う
    * [agda-stdlib](https://github.com/agda/agda-stdlib)
        * 所謂標準ライブラリ
    * [agda-prelude](https://github.com/UlfNorell/agda-prelude)
        * an alternative to the standard library
        * プログラミング重点
            * インスタンス変数等多用
        * 自然数に対するtactic
* Haskellへのマッピング等含めてスクラッチで与える
    * 暇な人ですか？

#
## 現実の入力を扱うには

* 標準入力をはじめ，多くの現実の入力の特徴
    * 終わりがいつかわからない
        * ソケット通信
        * /dev/random
    * 所謂，ストリーム

* agda-stdlibの遅延IOの型

~~~~
getContents : IO Costring
readFile : String → IO Costring
~~~~

* agda-preludeでは扱っていない
    * 終わりのわかっているファイルのみ

#
## Costringとは

* 文字の余リスト

~~~~
Costring : Set
Costring = Colist Char
~~~~

* (対して)Stringは何か特殊な型
    * 文字のリストと相互変換可能
    * HaskellではStringにマップされる

#
## Colistとは

* 終わらないかもしれないリスト構造
    * 一段階評価・分解し，始めて続くか終わるかがわかる
    * Coinductive Data Type

~~~~
data Colist {a} (A : Set a) : Set a where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A
~~~~

* (対して)Listは必ず終わりがあるリスト構造
    * 一段階ずつ`_∷_`して作られていることがわかっている
    * Inductive Data Type

~~~~
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
~~~~

#
## Coinductive - 3つの記号

~~~~
∞  : ∀ {a} (A : Set a) → Set a
♯_ : ∀ {a} {A : Set a} → A → ∞ A
♭  : ∀ {a} {A : Set a} → ∞ A → A
~~~~

* `∞`は delay operator
    * 中身が謎のヴェールに"包まれた"型かどうか
    * 評価が遅延するという意味を持つ型を作る
* `♯`は delay function
    * 謎のヴェールで"包む"
    * 評価を1段遅延させることを示す
* `♭`は force function
    * 謎のヴェールを"剥す"
    * 遅延させられた値の評価を1段進める

#
## 再掲: Colist

~~~~
data Colist {a} (A : Set a) : Set a where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A
~~~~

* Colistの値からパターンマッチで先頭`x`と残り`xs`が取り出せる
    * かもしれないし，もちろん`[]`かもしれない
* ただし，`xs`は`♭`してあげないとどうなっているかわからない
    * `xs`から次のパターンマッチはできない
    * `♭ xs`から次のパターンマッチができる

#
## Coinductiveで書けるもの

無限列

~~~~
ones : Colist ℕ
ones = 1 ∷ ♯ ones
~~~~

Listでは停止性検査にひっかかる

~~~~
ones : List ℕ
ones = 1 ∷ ones
~~~~

#
## 停止性の差異

OK

~~~~
del : ∀ {a} {A : Set a} → List A → List A
del [] = []
del (x ∷ xs) = del xs
~~~~

NG

~~~~
del : ∀ {a} {A : Set a} → Colist A → Colist A
del [] = []
del (x ∷ xs) = del (♭ xs)
~~~~

#
## 停止性検査が見ているもの

* Inductive Data に対する再帰
    * 引数の値の構造が小さくなるべき
    * 結果の値のコンストラクトが無限ループしないように
* Coinductive Data に対する(余)再帰
    * 結果の値の構造が大きくなるべき
    * 引数の値のパターンマッチが無限ループしないように

このあたりはIdrisとかでも同じ

#
## もう少し具体例:List上のfilter

Listのfilterは停止性判定を通る

~~~~
filter : ∀ {a} {A : Set a} →
         (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false =     filter p xs
~~~~

#
## もう少し具体例:Colist上のfilter

Colistのfilterは停止性判定を通らない

~~~~
filter : ∀ {a} {A : Set a} →
         (A → Bool) → Colist A → Colist A
filter p [] = []
filter p (x ∷ xs) with p x
... | true  = x ∷ ♯ filter p (♭ xs)
... | false =       filter p (♭ xs)
~~~~

#
## Coinductiveでは

* 構造を小さくするような関数定義は停止性検査を通らない
* 実用上有用なものは多い
    * 不要な要素を除去する filter
    * 複数の要素(文字)をまとめる lines
    * あれもこれも

#
## Colist上のfilterが作る構造

~~~~
1 ∷ (♯ 2 ∷ (♯ 3 ∷ (♯ 4 ∷ (♯ 5 ∷ (♯ 6 ∷ ♯ [])))))
~~~~

↓

Colist ℕ 上で奇数の filter

↓

~~~~
1 ∷        (♯ 3 ∷        (♯ 5 ∷        ♯ []))
~~~~

小さくなるので停止性検査を通らない

#
## HaskellのList

* AgdaのList Charでは実現できない
    * 全く遅延が無い
* AgdaのColist Charでは実現できない
    * 一部の関数の停止性が示せない

HaskellのListの正体とは？

#
## Partiality Monad の導入

* Partiality Monad
    * `now`と`later`による構造`_⊥`でモナド
    * agda-stdlibにも入っている

~~~~
data _⊥ {a} (A : Set a) : Set a where
  now   : (x : A) → A ⊥
  later : (x : ∞ (A ⊥)) → A ⊥
~~~~

#
## 停止性の変化

NG(再掲)

~~~~
del : ∀ {a} {A : Set a} → Colist A → Colist A
del [] = []
del (x ∷ xs) = del (♭ xs)
~~~~

OK

~~~~
del : ∀ {a} {A : Set a} → Colist A → Colist A ⊥
del [] = now []
del (x ∷ xs) = later (♯ del (♭ xs))
~~~~

#
## Colist⊥上のdelが作る構造

~~~~
now (1 ∷ now (2 ∷ now (3 ∷ now (4 ∷ now []))))
~~~~

↓

Colist ℕ ⊥ 上の del

↓

~~~~
later (♯ later (♯ later (♯ later (♯ now []))))
~~~~

delは小さくならないので停止性検査を通る

だが，これでもまだfilterは定義できない

#
## 新リスト型

全体とtailが個々にPartiality Monadに包まれている

~~~~
mutual
  data [_]' {a} (A : Set a) : Set a where
    []    : [ A ]'
    _∷_   : (x : A) (xs : [ A ]) → [ A ]'

  [_] : ∀ {a} → Set a → Set a
  [ A ] = [ A ]' ⊥
~~~~

この型が最もHaskellのリストに近い？

#
## [_]上のfilterの定義

停止性判定OK

~~~~
filter : ∀ {a} {A : Set a} → (A → Bool) → [ A ] → [ A ]
filter p (now [])   = now []
filter p (now (x ∷ xs)) with p x
... | true          = now (x ∷ filter p xs)
... | false         = later (♯ filter p xs)
filter p (later xs) = later (♯ filter p (♭ xs))
~~~~

#
## [_]上のfilterが作る構造

~~~~
now (1 ∷ now (2 ∷ now (3 ∷
  now (4 ∷ now (5 ∷ now (6 ∷ now []))))))
~~~~

↓

[ ℕ ] 上で奇数の filter

↓

~~~~
now (1 ∷ later (♯ now (3 ∷
  later (♯ now (5 ∷ later (♯ now []))))))
~~~~

小さくならないので停止性検査を通る

#
## 各リスト構造と評価

* List A
    * リスト構造全体が評価済みに相当
* Colist A
    * 先頭のみ評価済み，tailが1段階のみ遅延
* Colist A ⊥
    * 先頭のみ任意段階遅延，tailが1段階のみ遅延
* [ A ]
    * リスト構造全体が任意段階遅延

#
## linesの定義

停止性判定OK

~~~~
lines : [ Char ] → [ String ]
lines = go "" where
  go : String → [ Char ] → [ String ]
  go acc (now []) with acc ≟ ""
  ... | yes _      = now []
  ... | no  _      = now (acc ∷ now [])
  go acc (now (x ∷ xs)) with x Data.Char.≟ '\n'
  ... | yes _      = now (acc ∷ go "" xs)
  ... | no  _      = later (♯ go (acc ++ fromList Data.List.[ x ]) xs)
  go acc (later x) = later (♯ go acc (♭ x))
~~~~

#
## linesの構造

~~~~
now ('A' ∷ now ('B' ∷ now ('\n' ∷
  now ('C' ∷ now ('\n' ∷ now ('D' ∷ now []))))))
~~~~

↓

[ Char ] 上のlines

↓

~~~~
later (♯   later (♯   now ("AB" ∷
  later (♯   now ("C" ∷  later (♯ now ("D" ∷ now [])))))))
~~~~

小さくならないので停止性検査を通る

#
## agda-practical

[https://github.com/notogawa/agda-practical](https://github.com/notogawa/agda-practical)

* agda-stdlibベースのalt stdlib
* Haskellと同様に書けること重点
* agda-preludeと異なり遅延も扱う
* agda-preludeと異なりagda-stdlibと併用できる

#
## uniqの実現

agda-practicalを利用

~~~~
uniq : [ String ] → [ String ]
uniq = go nothing where
  go : Maybe String → [ String ] → [ String ]
  go mx (now []) = now []
  go mx (now (x ∷ xs)) with mx ≟ just x
  ... | yes _ = go mx xs
  ... | no  _ = now (x ∷ go (just x) xs)
  go mx (later x) = later (♯ go mx (♭ x))

main = run (interact (unlines ∘ map (fromList ∘ toList) ∘ uniq ∘ lines))
~~~~

#
## 証明もしてみよう

* Coinduction を含む証明
    * Induction に比べて難しい
    * 証明オブジェクトの構成にも停止性は必要
    * しかも，[_]上の証明では混在
* Partiality Monad を含む証明
    * 評価の各ステップを詳細に追うような
    * しかも，[_]上の証明では混在


1. Prop1 : uniq 空リスト = 空リスト
2. Prop2 : uniqの結果，隣接2要素は違うものになる
3. Prop3 : uniqの結果，元のリストの部分リストになる

#
## Prop1の証明

空リストに評価される値ならば，uniqしても空リストに評価される

~~~~
prop1 : ∀ xss → xss ⇓ [] → uniq xss ⇓ []
prop1 ._ (Equality.now x∼y) rewrite x∼y = Equality.now PropEq.refl
prop1 ._ (Equality.laterˡ {x = x} x₁) = Equality.laterˡ (uniq[]-is-[] (♭ x) x₁)
~~~~

これはカンタン

agda-stdlib定義済みのアレコレが助かる

#
## 性質Uniq

隣接2要素が異なるという性質

~~~~
data Uniq : [ String ] → Set where
  nil : Uniq (now [])
  singleton : ∀ {xs} → Uniq (now (xs ∷ now []))
  cons : ∀ {xs ys yss} → xs ≢ ys →
         Uniq (now (ys ∷ yss)) →
         Uniq (now (xs ∷ now (ys ∷ yss)))
  later1 : ∀ {xss} → ∞ (Uniq (♭ xss)) →
           Uniq (later xss)
  later2 : ∀ {xs xss} → ∞ (Uniq (now (xs ∷ ♭ xss))) →
           Uniq (now (xs ∷ later xss))
~~~~

<aside class="notes">
空リストはUniq
要素が1つのリストはUniq
Uniqなリストに，その先頭と違う要素を付けたリストもUniq
評価結果がUniqなリストの，先頭2要素が未評価な状態もまたUniq
</aside>

#
## Uniqのtest

証明できる

~~~~
-- [ "a", "b", "c" ] が Uniq
test-Uniq-1 : Uniq (later (♯ (now ("a" ∷ later (♯ now ("b" ∷ now ("c" ∷ now [])))))))
test-Uniq-1 = later1 (♯ later2 (♯ cons (λ ()) (cons (λ ()) singleton)))
~~~~

(命題が間違ってるので当然)証明できない

~~~~
-- [ "a", "a", "c" ] が Uniq
test-Uniq-2 : Uniq (later (♯ (now ("a" ∷ later (♯ now ("a" ∷ now ("c" ∷ now [])))))))
test-Uniq-2 = later1 (♯ later2 (♯ cons {!"a" ≢ "a"!} (cons (λ ()) singleton)))
~~~~

#
## Prop2の証明

~~~~
prop2 : ∀ xss → Uniq (uniq xss)
prop2 = lemma nothing where
  lemma : ∀ mxs xss → Uniq (go mxs xss)
  lemma mxs (now []) = nil
  lemma mxs (now (xs ∷ now [])) with mxs ≟ just xs
  lemma mxs (now (xs ∷ now [])) | yes p = nil
  lemma mxs (now (xs ∷ now [])) | no ¬p = singleton
  lemma mxs (now (xs ∷ now (ys ∷ yss))) with mxs ≟ just xs
  lemma mxs (now (xs ∷ now (ys ∷ yss))) | yes p = lemma mxs (now (ys ∷ yss))
  lemma mxs (now (xs ∷ now (ys ∷ yss))) | no ¬p with just xs ≟ just ys
  lemma mxs (now (xs ∷ now (ys ∷ yss))) | no ¬p | yes (just x≈y) rewrite x≈y = lemma nothing (now (ys ∷ yss))
  lemma mxs (now (xs ∷ now (ys ∷ yss))) | no ¬p₁ | no ¬p = cons (λ z → ¬p (just z)) (lemma nothing (now (ys ∷ yss)))
  lemma mxs (now (xs ∷ later xss)) with mxs ≟ just xs
  lemma mxs (now (xs ∷ later xss)) | yes p = lemma mxs (later xss)
  lemma mxs (now (xs ∷ later xss)) | no ¬p = later2 (♯ lemma nothing (now (xs ∷ ♭ xss)))
  lemma mxs (later xss) = later1 (♯ lemma mxs (♭ xss))
~~~~

#
## 性質Subseq

ある列(子)がある列(親)の部分列になっているという性質

~~~~
data Subseq : [ String ] → [ String ] → Set where
  nil : Subseq (now []) (now [])
  here : ∀ {xs xss ys yss} → xs ≡ ys →
         Subseq xss yss →
         Subseq (now (xs ∷ xss)) (now (ys ∷ yss))
  there : ∀ {xs xss yss} → Subseq xss yss →
          Subseq (now (xs ∷ xss)) yss
  laterₗ : ∀ {xss yss} → ∞ (Subseq (♭ xss) yss) →
           Subseq (later xss) yss
  laterᵣ : ∀ {xss yss} → ∞ (Subseq xss (♭ yss)) →
           Subseq xss (later yss)
~~~~

<aside class="notes">
空リスト同士はSubseq
Subseqなリスト同士の先頭に同じものを付けたリスト同士もSubseq
Subseqなリスト同士の親側だけに何かを付けたリスト同士もSubseq
評価結果がSubseqなリスト同士の，どちらかた未評価未評価な状態もまたSubseq
</aside>

#
## Prop3の証明

~~~~
prop3 : ∀ xss → Subseq xss (uniq xss)
prop3 = lemma nothing where
  lemma : ∀ mxs xss → Subseq xss (go mxs xss)
  lemma mxs (now []) = nil
  lemma mxs (now (xs ∷ now [])) with mxs ≟ just xs
  lemma mxs (now (xs ∷ now [])) | yes p = there nil
  lemma mxs (now (xs ∷ now [])) | no ¬p = here PropEq.refl nil
  lemma mxs (now (xs ∷ now (ys ∷ yss))) with mxs ≟ just xs
  lemma mxs (now (xs ∷ now (ys ∷ yss))) | yes p = there (lemma mxs (now (ys ∷ yss)))
  lemma mxs (now (xs ∷ now (ys ∷ yss))) | no ¬p = here PropEq.refl (lemma (just xs) (now (ys ∷ yss)))
  lemma mxs (now (xs ∷ later xss)) with mxs ≟ just xs
  lemma mxs (now (xs ∷ later xss)) | yes p = there (laterₗ (♯ laterᵣ (♯ (lemma mxs (♭ xss)))))
  lemma mxs (now (xs ∷ later xss)) | no ¬p = here PropEq.refl (laterₗ (♯ laterᵣ (♯ (lemma (just xs) (♭ xss)))))
  lemma mxs (later x) = laterₗ (♯ laterᵣ (♯ lemma mxs (♭ x)))
~~~~

#
## 証明もできた

* Coinduction を含む証明
    * 慣れれば難しくない
* Partiality Monad を含む証明
    * 慣れれば難しくない


* <strong style="color: #F00">慣れれば難しくない！</strong>

#
## 得られた知見

* データ構造移植
* laterの蓄積と消化
* 証明に使う性質の定義
* プログラミング全体の流れ

#
## データ構造移植

* Haskellから遅延評価込みでのデータ構造の移植
    * 再帰的な定義を全て Partiality Monad で包む
    * そのまま(Co)Inductiveなだけの定義に移すと大変かも

~~~~
mutual
  data [_]' {a} (A : Set a) : Set a where
    []    : [ A ]'
    _∷_   : (x : A) (xs : [ A ]) → [ A ]'

  [_] : ∀ {a} → Set a → Set a
  [ A ] = [ A ]' ⊥
~~~~

木構造や他の構造でも恐らく同じ

#
## laterの蓄積と消化

* 遅延のためのlaterが値の随所に溜まっていく
* 値は変換を繰り返し最終的には出力されるはず
    * 使われないならどうでもいい
    * 使われるなら最後はIO
* 出力時にreturn tt等の「何もしない」IOに変換・実行

~~~~
sequence : ∀ {a} {A : Set a} → [ IO A ] → IO [ A ]
sequence (now [])       = return (now [])
sequence (now (c ∷ cs)) = ♯ c              >>= λ x  →
                          ♯ (♯ sequence cs >>= λ xs →
                          ♯ return (now (x ∷ xs)))
sequence (later cs)     = ♯ sequence (♭ cs) >>= λ xs →
                          ♯ return (later (♯ xs))
~~~~

#
## 証明に使う性質の定義

* 各コンストラクタにdisjointな結果を構成させる
    * Inductive Data上の証明に対しても同様
    * nowとlaterが出てくるとなおさら

~~~~
data Uniq : [ String ] → Set where
  nil : Uniq (now [])
  singleton : ∀ {xs} → Uniq (now (xs ∷ now []))
  cons : ∀ {xs ys yss} → xs ≢ ys →
         Uniq (now (ys ∷ yss)) →
         Uniq (now (xs ∷ now (ys ∷ yss)))
  later1 : ∀ {xss} → ∞ (Uniq (♭ xss)) →
           Uniq (later xss)
  later2 : ∀ {xs xss} → ∞ (Uniq (now (xs ∷ ♭ xss))) →
           Uniq (now (xs ∷ later xss))
~~~~

* 興味ある人は性質Uniqを別の定義にして証明にトライ

#
## プログラミング全体の流れ

1. Costringを入力として受ける
2. agda-practicalのCharリストに変換する
3. Inductive Dataのリストに変換したりする
4. そのまま，あるいはInductive Data上で処理
5. (必要な箇所に証明を付ける)
6. Charリストに変換する
7. laterを消化しつつ出力する

agda-practicalのinteractは，
3～6を行う関数をもらって1,2,7を行う

#
## まとめ

* 去年の発表時のつらみはだいぶ解消
    * 動かし方は「全部Agdaで書く」に軍配
* agda-practical という形にしてみた
* プログラミングのコツをつかんできた
    * IOを扱い
    * Coinductive Data を扱い
    * 停止性を満たし
    * 証明も与える

#
## 今後の課題

* Lazy IO に依らない Streaming Data Processing
    * 適切なリソースの扱い
    * conduit/pipes系の移植？
* Partiality Monad が Monad Transformer の相性
    * 合成してもlaterが綺麗に扱えない
* agda-practical の充実
    * parser系を用意しないと数値等に変換できない
    * プロコンでAgdaを使えるくらいには

~~~~
オレは ようやく のぼりはじめた ばかりだからな

この はてしなく遠い Agda坂をよ…
~~~~

#
## 以上

Agda実用勢からの Pull Request 等お待ちしてます

[https://github.com/notogawa/agda-practical](https://github.com/notogawa/agda-practical)
