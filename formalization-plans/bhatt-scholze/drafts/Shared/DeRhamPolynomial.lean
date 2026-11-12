-- 将来の置き場所：共有層（CommutativeAlgebra/DeRham/Polynomial など。調整役と相談）。BS 固有ではない。
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §2.1、G-A1-9、D26。基準コミット 972bb7f53。ビルドしない。
module

-- 取り込み時の依存先：drafts/DerivedGeneral/{CompletionFunctor,Truncation}.lean。
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty
public import SerrePositivity.CommutativeAlgebra.DeRham.CompletedLeibniz
public import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# 多項式代数の de Rham 複体とその普遍性

## 概要
可換環 k と有限集合 T 上の多項式代数 P = k[X_t] について、de Rham 複体 Ω^•_{P/k}：Ω^i は P 上の自由加群（基底 dX_{t_1} ∧ ⋯ ∧ dX_{t_i}）、
微分 d(f dX_I) = Σ_t (∂f/∂X_t) dX_t ∧ dX_I。可換 dg 代数（外積）で、Ω^* = Λ^*_P(Ω^1)。普遍性：次数付き可換 dg k 代数 H^* への
dg 代数の射 Ω^* → H^* は、環の射 η^0 : P → H^0 と、P 線形な η^1 : Ω^1 → H^1 で η^1(df) = d_H(η^0 f) かつ η^1(ω)² = 0 を満たすものから一意に決まる。
p 完備化した多項式代数 P^∧ については Ω^i_{P^∧} := P^∧ ⊗_P Ω^i_P（有限自由なので完備化と同じ）と d の延長。

## 方針
Ω^1 を `ExteriorAlgebra`／`exteriorPower` の上に載せ、普遍性は `ExteriorAlgebra.lift`（平方零の線形写像からの代数射）と、
微分との両立を生成元で確かめることから。偏微分は Mathlib の `MvPolynomial.pderiv`。

## 規約
T は `Fintype`。原典の Ω^i_{R/(A/I)} は p 進形式スキームの連続微分で、p 完備多項式代数では dX 上の自由加群（D26）。
Mathlib の `KaehlerDifferential` との一致は注記（必要になれば定理に）。Cartier 同型は別ファイル（A1-3）。

## 使われ方
Constr 4.9（η^*）、Thm 4.11 の主張、Cor 5.5（Cartier）、Thm 5.2 の β 形（pd 包の Čech 脈体 ≃ de Rham 複体）、A2 の HT filtration。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open scoped DirectSum

namespace SerrePositivity.DeRham

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T]

/-- 概要：de Rham cohomology の積 H^i × H^j → H^{i+j}（外積から）。
方針：`deRhamD_wedge` により外積は余輪体 × 余輪体を余輪体へ、余境界 × 余輪体を余境界へ送る。
規約：11-07 追加。
使われ方：A1/CrystallineInput の Cartier 同型の乗法性、段 4・6。 -/
def deRhamCohomologyWedge {i j : ℕ} :
    (deRhamComplex k T).homology i → (deRhamComplex k T).homology j → (deRhamComplex k T).homology (i + j) :=
  sorry -- 外積を余輪体の代表で取り、deRhamD_wedge で well-defined

/-! ## p 完備化 -/

/-! 概要：p 完備化した多項式代数 P^∧ = k⟨X_T⟩ 上の微分形式 Ω^i_{P^∧} := P^∧ ⊗_P Ω^i_P（有限自由）。
方針：係数拡大。d は **k 線形な連続微分**として完備化へ延びる（偏微分の連続性）。P^∧ 線形ではない（d(X) = dX ≠ X·d(1) = 0、W9-I-22）。外積は P^∧ 線形。
規約：原典の Ω^i_{R/(A/I)}（R = A/I⟨X⟩）はこれ（D26）。
使われ方：A1 の HT 比較の対象 R = (A/d)⟨X⟩。
**D4-01（11-03、BS-D4 の質問への回答）**：これは **H⁰ の（古典的）完備化**で、A1 の有界 prism（k = A/d は有界 p 冪ねじれ）では導来 p 完備化と一致する。
A2 の HT filtration（一般の k、D(k)_{p-comp} 内）では H⁰ を取ると導来完備化の負次数を失う（k の p 冪ねじれが有界でないと LΛ_p(自由加群) は離散でない）ので、
A2 は通常の `forms` を `discreteModuleEmbedding` で D(k) に入れて DerivedGeneral の `completion`（LΛ_p）を施した対象を使い、有界 p 冪ねじれの下でだけ `completedForms` と同定する
（`completedForms_eq_derivedCompletion_of_boundedTorsion`）。k⟨X_T⟩ は `PrincipalCompletionH0 (Poly k T) p`（E3 の `completionRing` と同じ道具）。 -/
open SerrePositivity.InfinityCategories

/-- 概要：k の p 冪ねじれが有界（例：有界 prism の A/d）なら、`forms k T i` の導来 p 完備化（DerivedGeneral `completion`、D(k) の対象）は離散で、
`completedForms k T p i` の `discreteModuleEmbedding` の像と `VertexIso`。A1 はこの同定で設計の Ω̂ を使い、A2 は導来側を使う。
方針：有界ねじれの自由加群の導来完備化は離散で古典的完備化（a0-design §5.1 の 1 の計算と同じ）。
規約：有界性は IsBoundedPrism と同じ一様な指数。完備化の生成元は一元集合。
使われ方：A1-1・A1-3（Ω̂）、A2 HodgeTateFiltration の gr との比較。 -/
def completedForms_eq_derivedCompletion_of_boundedTorsion (p i : ℕ)
    (hk : ∃ N : ℕ, ∀ (n : ℕ) (x : k), (p : k)^n * x = 0 → (p : k)^N * x = 0) :
    VertexIso ((completion k {(p : k)}).app _ ((discreteModuleEmbedding k).app _
      (nerveVertex (ModuleCat.of k (forms k T i)))))
      ((discreteModuleEmbedding k).app _ (nerveVertex (ModuleCat.of k (completedForms k T p i)))) := by
  sorry -- 多項式形式は多項式環上有限自由。係数のねじれの一様な上界により導来完備化は次数零

end SerrePositivity.DeRham
