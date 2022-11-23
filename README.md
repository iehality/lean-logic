# lean-logic
Lean3で論理学を形式化する

## 構造
  - `provability.lean`
  - `logic.lean`
  - `consistency.lean`
### lib
  - `notation.lean`：ノーテーション
  - `tukey.lean`：テューキーの補題
  - `lib.lean`
### PL：命題論理
  - `pl.lean`：命題論理の言語, 項, 論理式
  - `deduction.lean`：演繹体系
  - `semantics.lean`：モデルと意味論
### FOL：1階論理
  - `fol.lean`：一階論理の言語, 項, 論理式
  - `theory.lean`：理論に関する証明
  - `deduction.lean`：演繹体系
  - `semantics.lean`：モデルと意味論
  - `lindenbaum.lean`：一階論理のリンデンバウム代数
  - `ultraproduct.lean`：超積, 超冪
  - `translation.lean`：異なる言語感の関係
  - `language_extention.lean`：言語の拡大に関する証明
  - `consisyency.lean`：無矛盾な理論に関する証明
  - `completeness.lean`：完全性定理の証明
  - `pnf.lean`：冠頭標準形に関する証明
  - `class_of_formulae.lean`：論理式のクラス
  - `arithmetic.lean`：算術に関する証明
  - ~~`model.lean`：超準モデルの構成など~~

### QL：Quantificational Logic
  - ### FOL：FOLのリファクタリング及び修正

## 定義
### 命題論理
- ヒルベルト流演繹体系
  - `(⊢)`
- 構造, モデル
  - `pl.Structure`
  - `(⊧)`
### 1階論理
- ヒルベルト流演繹体系
  - `(⊢)`
- 構造, モデル
  - `fol.Structure`
  - `(⊧)`
- 理論
  - `𝐐`
  - `𝐈ₒₚₑₙ`
  - `𝐈𝛴`
  - `𝐏𝐀`, ...

## 証明
- 命題論理の健全性定理
  - `pl.soundness : T ⊢ p → T ⊧ p`
- 命題論理の完全性定理
  - `pl.completeness : T ⊢ p ↔ T ⊧ p`
- 1階論理の健全性定理
  - `fol.soundness : T ⊢ p → T ⊧ p`
- Łośの定理
  - `fol.Ult.fundamental : ℿ 𝔄 ⫽ F ⊧ p ↔ {i | 𝔄 i ⊧ p} ∈ F`
  - `fol.Ult.fundamental_param : ∀ (p : formula L) (e : ∀ i, ℕ → |𝔄 i|), ℿ 𝔄 ⫽ F ⊧[λ n, ⟦λ i, e i n⟧*] p ↔ {i | 𝔄 i ⊧[e i] p} ∈ F`
- 1階論理のコンパクト性定理
  - `fol.compactness.compact (T : theory L) : Satisfiable T ↔ ∀ S : finset (formula L), ↑S ⊆ T → Satisfiable S`
- 1階論理の完全性定理
  - `fol.completeness {p : formula L} (hp : is_sentence p) : T ⊢ p ↔ T ⊧ p`  
  - `fol.completeness' {p : formula L} : T ⊢ p ↔ T ⊧ p :=`

## TODO
  - 算術の$\Sigma_1$完全性
  - メタ数学の算術化
  - ゲーデルの不完全性定理

## 参考文献
  - mathlib https://github.com/leanprover-community/mathlib
  - ケネス・キューネン, 藤田 博司 訳, キューネン数学基礎論講義
  - 田中 一之, 数学基礎論序説: 数の体系への論理的アプローチ
  - 田中 一之, 計算理論と数理論理学
  - Petr Hajek, Metamathematics of First-Order Arithmetic
  - flypitch https://flypitch.github.io/