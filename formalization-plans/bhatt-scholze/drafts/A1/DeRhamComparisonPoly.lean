-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.DeRhamComparisonPoly（仮。原典 Thm 6.4 の多項式・mod p の場合）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §9、単位 A1-5。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
-- 本ファイルは drafts/A1/{CrystallineInput,HodgeTateComparison,HodgeTateMap}.lean、drafts/Shared/DeRhamPolynomial.lean、drafts/A2/BaseChangeAndTensor.lean、
-- drafts/A5/RootAdjunction.lean（`polyRootAlgebra`。W9-III-09：WeaklyInitialAndDescent ではなく先行ファイル）を import する。
-- 結晶の黒箱 `crystalline_deRham_polynomial_Zp` と Cartier は drafts/A1/CrystallineInput.lean に切り出した（W9-III-09：HodgeTateComparison がそれを使うため）。

/-!
# de Rham 比較の多項式・mod p の場合（BS 著者版 Thm 6.4 の特別な場合、A1-5）

## 概要
完全 prism (A,(d))、R = A/d、T = R⟨X_1,…,X_n⟩ について φ_A^*Δ_{T/A} ⊗̂^L_A A/(p,d) ≃ Ω^*_{(T/p)/(R/p)}（D(R/p) の可換代数の自然な同型）。
T_∞ = R⟨X_i^{1/p^∞}⟩ では ≃ T_∞/p。Lemma 8.6（A5-3）の入力。

## 方針
Prop 6.2 と同じ帰着（D69）：完全 prism → 普遍向き付き prism A_0（(4)）→ 結晶 prism D_0（Construction 6.1 の α、保存性と (3)）→ Z_p（Lemma 4.20）
→ 結晶の黒箱（Thm 5.2 β の de Rham 形、D68）。可換代数構造は各段で保つ。

## 規約
Frobenius 捻り φ^*Δ ⊗ A/(p,d) = Δ ⊗_A A/(p, φ^{-1}(d))（完全 prism）。de Rham 複体は Shared/DeRhamPolynomial の cdga を CAlg に。

## 使われ方
A5-3 `rootMap_modP_eq_deRham`。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime]

/-- 概要：結晶 prism (B,(p)) と多項式 (B/p)[X]：Lemma 4.20（(p)-prism の Δ は p 完備底変換と可換、A0-4）で Z_p に帰着。 -/
theorem deRham_iso_polynomial_crystalline : True := by trivial

/-- 概要：普遍向き付き prism A_0 上の比較同型（原典 Thm 6.4 の証明そのもの、D69 訂正後）：A_0/d_0 は p ねじれなし（Ex 3.4）なので W(A_0/d_0) も p ねじれなし。
ψ := F ∘ can : A_0 → W(A_0/d_0) は prism の射 (A_0,(d_0)) → (W(A_0/d_0),(p))、底変換 (4) で Δ_{T_0/A_0} ⊗̂_{A_0,ψ} W ≅ Δ_{T′/W}、Thm 5.2 β（pd イデアル J つき）で
RΓ_crys、持ち上げの de Rham 複体 Ω^*_{T_0/(A_0/d_0)} に自然に同型。
方針：`deRham_iso_polynomial_crystalline`、A0-4 の底変換、W9-I-15（保存性だけでは比較射が作れない）。
規約：CAlg の自然な同型。 -/
theorem deRham_iso_polynomial_universal : True := by trivial

/-- 概要：A1-5 の主張：完全 prism (A,(d))、T = R⟨X_1..X_n⟩ で φ_A^*Δ_{T/A} ⊗̂^L_A A/(p,d) ≃ Ω^*_{(T/p)/(R/p)}（CAlg(D(R/p))、T について自然）。
方針：d の選択で A_0 → A、`deRham_iso_polynomial_universal` の比較同型を (4) で底変換（Frobenius と両立、紙 1）。保存性は使わない。
規約：Lemma 8.6 で使う形は Δ_T ⊗_A A/(p, φ^{-1}(d))。
使われ方：A5-3。 -/
theorem deRham_iso_polynomial_modP (n : ℕ) : True := by trivial

/-- 概要：T_∞ = R⟨X_i^{1/p^∞}⟩：φ^*Δ_{T_∞} ⊗ A/(p,d) ≃ T_∞/p（T_∞ = (colim_m T_m)^∧、Δ は filtered 余極限と可換、Ω^{≥1} の遷移 d(X^{1/p^m}) = 0 で消える）。
方針：`deRham_iso_polynomial_modP` を各 T_m に、A5-4 の filtered 余極限（紙 3）。
使われ方：A5-3（F = fib の計算）。 -/
theorem deRham_iso_rootAlgebra_modP (n : ℕ) : True := by trivial

end SerrePositivity.BhattScholze.Prismatic
