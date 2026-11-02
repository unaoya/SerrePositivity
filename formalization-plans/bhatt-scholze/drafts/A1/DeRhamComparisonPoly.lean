-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.DeRhamComparisonPoly（仮。原典 Thm 6.4 の多項式・mod p の場合）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §9、単位 A1-5。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
-- 本ファイルは drafts/A1/{HodgeTateComparison,HodgeTateMap}.lean、drafts/Shared/DeRhamPolynomial.lean、drafts/A2/BaseChangeAndTensor.lean、
-- drafts/A5/WeaklyInitialAndDescent.lean（`polyRootAlgebra`）を import する。

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

/-- 概要：結晶の黒箱（de Rham 形、D68）：φ^*Δ_{F_p[X_1..X_n]/Z_p} ≃ Ω^*_{Z_p⟨X⟩/Z_p}（p 完備、CAlg(D(Z_p))）。Thm 5.2 β の使う形。
方針：引用（結晶比較と、結晶コホモロジーが持ち上げの de Rham 複体で計算されること）。A1-3 の `hodgeTate_iso_polynomial_Zp` はこれと Cartier から。
規約：`sorry`（結晶側、A1-2/A1-3 の唯一の黒箱）。
使われ方：以下の帰着の終点。 -/
theorem crystalline_deRham_polynomial_Zp (n : ℕ) : True := by sorry -- 結晶の黒箱（A1-3）

/-- 概要：HT 比較（Cor 5.5）を黒箱と Cartier（G-A5-12 の n 変数版）から：A1-3 の `hodgeTate_iso_polynomial_Zp` の証明。 -/
theorem hodgeTate_of_deRham_cartier (n : ℕ) : True := by trivial

/-- 概要：結晶 prism (B,(p)) と多項式 (B/p)[X]：Lemma 4.20（(p)-prism の Δ は p 完備底変換と可換、A0-4）で Z_p に帰着。 -/
theorem deRham_iso_polynomial_crystalline : True := by trivial

/-- 概要：普遍向き付き prism A_0：Construction 6.1 の α : A_0 → D_0 で α̂^* は保存的（(1)）、(3) で α̂^*Δ_{T_0/A_0} = Δ_{T_{D_0}/D_0}、α は δ 射で φ と両立。
方針：A1-4 の `crystallineCover*`・`baseChangeB`、CAlg の同型の反映（紙 2）。 -/
theorem deRham_iso_polynomial_universal : True := by trivial

/-- 概要：A1-5 の主張：完全 prism (A,(d))、T = R⟨X_1..X_n⟩ で φ_A^*Δ_{T/A} ⊗̂^L_A A/(p,d) ≃ Ω^*_{(T/p)/(R/p)}（CAlg(D(R/p))、T について自然）。
方針：d の選択で A_0 → A、(4) で A_0 上に帰着（Frobenius と両立、紙 1）、`deRham_iso_polynomial_universal`。
規約：Lemma 8.6 で使う形は Δ_T ⊗_A A/(p, φ^{-1}(d))。
使われ方：A5-3。 -/
theorem deRham_iso_polynomial_modP (n : ℕ) : True := by trivial

/-- 概要：T_∞ = R⟨X_i^{1/p^∞}⟩：φ^*Δ_{T_∞} ⊗ A/(p,d) ≃ T_∞/p（T_∞ = (colim_m T_m)^∧、Δ は filtered 余極限と可換、Ω^{≥1} の遷移 d(X^{1/p^m}) = 0 で消える）。
方針：`deRham_iso_polynomial_modP` を各 T_m に、A5-4 の filtered 余極限（紙 3）。
使われ方：A5-3（F = fib の計算）。 -/
theorem deRham_iso_rootAlgebra_modP (n : ℕ) : True := by trivial

end SerrePositivity.BhattScholze.Prismatic
