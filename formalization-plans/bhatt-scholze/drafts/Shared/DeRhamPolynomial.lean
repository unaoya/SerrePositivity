-- 将来の置き場所：共有層（CommutativeAlgebra/DeRham/Polynomial など。調整役と相談）。BS 固有ではない。
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §2.1、G-A1-9、D26。基準コミット 972bb7f53。ビルドしない。
module

-- 取り込み時の依存先：drafts/DerivedGeneral/{CompletionFunctor,Truncation}.lean。
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import Mathlib.Algebra.MvPolynomial.PDeriv
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

namespace SerrePositivity.DeRham

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T]

/-- 概要：多項式代数 P = k[X_T]。
方針：`MvPolynomial`。
規約：—
使われ方：de Rham 複体の係数。 -/
abbrev Poly : Type u := MvPolynomial T k

/-- 概要：Ω^i_{P/k} := P ⊗_k Λ^i(k^T)（dX_t の i 次の外積が基底の自由 P 加群）。
方針：`exteriorPower k i (T → k)` を P 上に係数拡大。
規約：i > #T なら零。
使われ方：de Rham 複体の項。 -/
def forms (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (i : ℕ) : Type u :=
  sorry -- TensorProduct k (Poly k T) (exteriorPower k i (T → k))。11-03（BS-D4 の D4-01）：k・T を明示引数に（body が sorry だと section 変数が落ちる）

instance (i : ℕ) : AddCommGroup (forms k T i) := sorry
instance (i : ℕ) : Module (Poly k T) (forms k T i) := sorry
instance (i : ℕ) : Module k (forms k T i) := sorry

/-- 概要：dX_t ∈ Ω^1。
方針：1 ⊗ e_t。
規約：—
使われ方：η^1 の定義、Cartier の計算。 -/
def dX (t : T) : forms k T 1 := sorry

/-- 概要：外積 Ω^i × Ω^j → Ω^{i+j}。
方針：外積代数の積を P 線形に延ばす。
規約：次数付き可換（ω ∧ η = (−1)^{ij} η ∧ ω）。
使われ方：dg 代数の構造。 -/
def wedge {i j : ℕ} : forms k T i → forms k T j → forms k T (i + j) := sorry

/-- 概要：de Rham 微分 d : Ω^i → Ω^{i+1}、d(f dX_I) = Σ_t (∂_t f) dX_t ∧ dX_I。
方針：`MvPolynomial.pderiv` と `wedge`。
規約：d² = 0、Leibniz d(ω ∧ η) = dω ∧ η + (−1)^i ω ∧ dη。
使われ方：de Rham 複体。 -/
def deRhamD (i : ℕ) : forms k T i →+ forms k T (i + 1) := sorry

theorem deRhamD_comp (i : ℕ) (ω : forms k T i) : deRhamD k T (i + 1) (deRhamD k T i ω) = 0 := by
  sorry

theorem deRhamD_wedge {i j : ℕ} (ω : forms k T i) (η : forms k T j) :
    cast (by omega) (deRhamD k T (i + j) (wedge k T ω η)) =
      cast (by omega) (wedge k T (deRhamD k T i ω) η) + (-1 : ℤ) ^ i • wedge k T ω (deRhamD k T j η) := by
  sorry

/-- 概要：de Rham 複体 Ω^•_{P/k} を k 加群の余鎖複体として。
方針：`CochainComplex.of`。
規約：次数 i に Ω^i。
使われ方：H^i(Ω^•) と Cartier 同型。 -/
def deRhamComplex (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] : CochainComplex (ModuleCat.{u} k) ℕ :=
  sorry -- CochainComplex.of (fun i => ModuleCat.of k (forms k T i)) (deRhamD k T) (deRhamD_comp k T)。11-03（D4-05）：k・T を明示引数に

/-! ## 普遍性（Constr 4.9 の「universal property of the de Rham complex」） -/

/-- 概要：次数付き可換 dg k 代数（次数ごとの k 加群、結合的な積、次数付き可換性、微分と Leibniz）。H^*(Ō) の模型の型。
方針：必要な構造だけを構造体にする（Mathlib の dg 代数は使わない）。
規約：次数付き可換性は a·b = (−1)^{mn} b·a（奇数次の平方零は要求しない：p = 2 のため。Lemma 4.10 が別に要る）。
使われ方：η^* の標的。 -/
structure GradedCommDGAlgebra where
  carrier : ℕ → Type u
  [addCommGroup : ∀ n, AddCommGroup (carrier n)]
  [module : ∀ n, Module k (carrier n)]
  mul : ∀ {m n}, carrier m → carrier n → carrier (m + n)
  one : carrier 0
  d : ∀ n, carrier n →+ carrier (n + 1)
  -- 結合律・単位律・双線形性・次数付き可換性・d² = 0・Leibniz は略（骨組み）

/-- 概要：普遍性：環の射 η^0 : P → H^0 と、P 線形（H^0 を経由）な η^1 : Ω^1 → H^1 で、η^1(df) = d(η^0 f) かつ η^1(ω)·η^1(ω) = 0 となるものから、
dg 代数の射 Ω^* → H^* が一意に延びる。
方針：Ω^* = Λ^*_P(Ω^1) の外積代数の普遍性（`ExteriorAlgebra.lift`：平方零の線形写像から代数射）と、微分との両立を生成元で。
規約：平方零の条件は原典の Lemma 4.10（β(f)² = 0）に対応。
使われ方：Constr 4.9 の η^*。 -/
theorem exists_unique_dgHom (H : GradedCommDGAlgebra k)
    (η0 : Poly k T →+* H.carrier 0) (η1 : forms k T 1 →+ H.carrier 1)
    (hlin : True) -- 要確認：η^1 の P 線形性（H^0 の作用を η0 で）の述べ方
    (hd : ∀ f : Poly k T, η1 (deRhamD k T 0 (cast (by sorry) f)) = H.d 0 (η0 f))
    (hsq : ∀ ω : forms k T 1, H.mul (η1 ω) (η1 ω) = 0) :
    ∃! Φ : ∀ i, forms k T i →+ H.carrier i,
      (∀ f, Φ 0 (cast (by sorry) f) = η0 f) ∧ (∀ ω, Φ 1 ω = η1 ω) ∧
      (∀ {i j} (ω : forms k T i) (η : forms k T j), Φ (i + j) (wedge k T ω η) = H.mul (Φ i ω) (Φ j η)) ∧
      (∀ i ω, Φ (i + 1) (deRhamD k T i ω) = H.d i (Φ i ω)) := by
  sorry -- 外積代数の普遍性と生成元での検算

/-! ## p 完備化 -/

/-- 概要：p 完備化した多項式代数 P^∧ = k⟨X_T⟩ 上の微分形式 Ω^i_{P^∧} := P^∧ ⊗_P Ω^i_P（有限自由）。
方針：係数拡大。d は **k 線形な連続微分**として完備化へ延びる（偏微分の連続性）。P^∧ 線形ではない（d(X) = dX ≠ X·d(1) = 0、W9-I-22）。外積は P^∧ 線形。
規約：原典の Ω^i_{R/(A/I)}（R = A/I⟨X⟩）はこれ（D26）。
使われ方：A1 の HT 比較の対象 R = (A/d)⟨X⟩。
**D4-01（11-03、BS-D4 の質問への回答）**：これは **H⁰ の（古典的）完備化**で、A1 の有界 prism（k = A/d は有界 p 冪ねじれ）では導来 p 完備化と一致する。
A2 の HT filtration（一般の k、D(k)_{p-comp} 内）では H⁰ を取ると導来完備化の負次数を失う（k の p 冪ねじれが有界でないと LΛ_p(自由加群) は離散でない）ので、
A2 は通常の `forms` を `discreteModuleEmbedding` で D(k) に入れて DerivedGeneral の `completion`（LΛ_p）を施した対象を使い、有界 p 冪ねじれの下でだけ `completedForms` と同定する
（`completedForms_eq_derivedCompletion_of_boundedTorsion`）。k⟨X_T⟩ は `PrincipalCompletionH0 (Poly k T) p`（E3 の `completionRing` と同じ道具）。 -/
abbrev completedPoly (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ) : Type u :=
  SerrePositivity.DerivedCompletion.PrincipalCompletionH0 (Poly k T) (p : Poly k T)
def completedForms (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ) (i : ℕ) : Type u :=
  sorry -- completedPoly k T p ⊗_{Poly k T} forms k T i（有限自由なので = PrincipalCompletionH0 (forms k T i) p）
instance (p i : ℕ) : AddCommGroup (completedForms k T p i) := sorry
instance (p i : ℕ) : Module (completedPoly k T p) (completedForms k T p i) := sorry
instance (p i : ℕ) : Module k (completedForms k T p i) := sorry

open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.Derived

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

/-! ## 完備形式上の連続微分と外積（D4-05、11-03。A1 の Ω̂ の dg 構造） -/

/-- 概要：完備化単位 Ω^i → Ω̂^i（`forms k T i → completedForms k T p i`）。
方針：係数拡大 P → P^∧ に沿う。
規約：k 線形。
使われ方：連続微分の定義（稠密な像からの延長）。 -/
def completedFormsUnit (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p i : ℕ) :
    forms k T i →+ completedForms k T p i := sorry

/-- 概要：Ω̂ 上の外積 Ω̂^i × Ω̂^j → Ω̂^{i+j}（P^∧ 双線形、次数付き可換）。
方針：Ω̂^i = P^∧ ⊗_P Ω^i の有限自由性で `wedge` を係数拡大。
規約：`completedFormsUnit` と両立。
使われ方：dg 代数構造、Cartier、A1 の η^*。 -/
def completedWedge (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ) {i j : ℕ} :
    completedForms k T p i → completedForms k T p j → completedForms k T p (i + j) := sorry
theorem completedWedge_unit (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ) {i j : ℕ}
    (ω : forms k T i) (η : forms k T j) :
    completedWedge k T p (completedFormsUnit k T p i ω) (completedFormsUnit k T p j η) = completedFormsUnit k T p (i + j) (wedge k T ω η) := by
  sorry

/-- 概要：**k 線形な連続微分** d̂ : Ω̂^i → Ω̂^{i+1}（W9-I-22：P^∧ 線形ではない。d(X) = dX ≠ X·d(1)）。偏微分 ∂_t の p 進連続性で P → P^∧ の稠密な像から延びる。
方針：Ω̂^i = P^∧ ⊗_P Ω^i の元 f ⊗ ω（f ∈ P^∧）に d̂(f ⊗ ω) = Σ_t ∂_t f ⊗ (dX_t ∧ ω) + f ⊗ dω で定める（∂_t は P^∧ の連続微分、Cauchy 列ごと）。
規約：d̂² = 0、Leibniz、`completedFormsUnit` と両立（d̂ ∘ unit = unit ∘ d）。
使われ方：完備 de Rham 複体 Ω̂^•、A1 の HT 比較の標的側、A5 の G-A5-12。 -/
def completedDeRhamD (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p i : ℕ) :
    completedForms k T p i →+ completedForms k T p (i + 1) := sorry
theorem completedDeRhamD_unit (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p i : ℕ) (ω : forms k T i) :
    completedDeRhamD k T p i (completedFormsUnit k T p i ω) = completedFormsUnit k T p (i + 1) (deRhamD k T i ω) := by sorry
theorem completedDeRhamD_comp (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p i : ℕ) (ω : completedForms k T p i) :
    completedDeRhamD k T p (i + 1) (completedDeRhamD k T p i ω) = 0 := by sorry
theorem completedDeRhamD_wedge (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ) {i j : ℕ}
    (ω : completedForms k T p i) (η : completedForms k T p j) :
    cast (by omega) (completedDeRhamD k T p (i + j) (completedWedge k T p ω η)) =
      cast (by omega) (completedWedge k T p (completedDeRhamD k T p i ω) η) + (-1 : ℤ) ^ i • completedWedge k T p ω (completedDeRhamD k T p j η) := by
  sorry

/-- 概要：完備 de Rham 複体 Ω̂^•_{P^∧/k}（k 加群の余鎖複体。次数 i に Ω̂^i、微分は d̂）。A1 では CommMon (Complex k) にまとめて Barratt–Eccles の augmentation と
`cAlgVertex` で E∞ 代数に実現する（A1 側）。
方針：`CochainComplex.of`。
規約：k 線形複体（P^∧ 線形ではない）。
使われ方：A1 の HT 比較（Ω̂ = 原典の Ω_{R/(A/I)}、D26）、A1-5、G-A5-12。 -/
def completedDeRhamComplex (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ) : CochainComplex (ModuleCat.{u} k) ℕ :=
  sorry -- CochainComplex.of (fun i => ModuleCat.of k (completedForms k T p i)) (completedDeRhamD k T p) (completedDeRhamD_comp k T p)

end SerrePositivity.DeRham
