# lean-logic
Lean3で一階述語論理を形式化する

## 構造
  - `provable.lean`：命題論理
  - `fopl.lean`：一階論理の言語, 項, 論理式
  - `theory.lean`：理論に関する証明
  - `deduction.lean`：演繹体系に関する証明
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
  - `model.lean`：超準モデルの構成など

## 定義
- 一階述語論理の言語, 項, 論理式
  - `fopl.language`
  - `fopl.term`
  - `fopl.formula`
- ヒルベルト流演繹体系
  - `(⊢)`
- 構造, モデル
  - `fopl.model`
  - `(⊧)`
- 理論
  - `𝐐`
  - `𝐈ₒₚₑₙ`
  - `𝐈𝛴`
  - `𝐏𝐀`, ...

## 証明
- 一階論理の健全性定理
  - `fopl.soundness : T ⊢ p → ∀ {M}, M ⊧ₜₕ T → M ⊧ p`
- Łośの定理
  - `fopl.Ult.fundamental : ℿ 𝔄 ⫽ F ⊧ p ↔ {i | 𝔄 i ⊧ p} ∈ F`
  - `fopl.Ult.fundamental_param : ∀ (p : formula L) (e : ∀ i, ℕ → |𝔄 i|), ℿ 𝔄 ⫽ F ⊧[λ n, ⟦λ i, e i n⟧*] p ↔ {i | 𝔄 i ⊧[e i] p} ∈ F`
- 一階論理のコンパクト性定理
  - `fopl.compactness.compact (T : theory L) : (∃ 𝔄, 𝔄 ⊧ₜₕ T) ↔ (∀ S : finset (formula L), (∀ {p}, p ∈ S → p ∈ T) → ∃ 𝔄, 𝔄 ⊧ₜₕ {p | p ∈ S})`
- 一階論理の完全性定理
  - `fopl.completeness {p : formula L} (hp : is_sentence p) : T ⊢ p ↔ (∀ M, M ⊧ₜₕ T → M ⊧ p)`  
  - `fopl.completeness' {p : formula L} : T ⊢ p ↔ (∀ M, M ⊧ₜₕ T → M ⊧ p) :=`

## TODO
  - 算術の$\Sigma_1$完全性
  - メタ数学の算術化
  - ゲーデルの不完全性定理