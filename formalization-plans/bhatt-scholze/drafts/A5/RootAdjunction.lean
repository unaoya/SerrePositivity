-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction（仮。原典 Prop 8.5 の証明 (1)〜(3) で使う根添加の構成）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §3.1〜§3.3（定義の部分）、単位 A5-4。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
-- 本ファイルは drafts/A2/BaseChangeAndTensor.lean（完備テンソル）だけを import する。A1/DeRhamComparisonPoly・A5/StrongDescent・A5/WeaklyInitialAndDescent・
-- A6/ArcSite がこれを import する（W9-III-09：後段の降下の証明と同居させない）。

/-!
# 根添加の構成（BS 著者版 Prop 8.5 の証明 (1)〜(3) の定義部分）

## 概要
(1) 全元に p 乗根を mod p で添加する ω 段の S̃ = `rootClosure`（D51）とその延長性・濃度・関手性、(2) 完備化前の代数的な根添加 E(C) = `algebraicRootClosure`
（G-A5-18、filtered 余極限と可換）、(3) T_∞ = R⟨X_i^{1/p^∞}⟩ = `polyRootAlgebra` と S̃ = S ⊗̂_T T_∞ = `rootCover`。

## 方針
W9-III-09 で A5/WeaklyInitialAndDescent.lean から切り出した定義と初等的補題。semiperfectoid 性（`rootClosure_isSemiperfectoid`・`rootCover_isSemiperfectoid`、
`IsSemiperfectoid` は SemiperfectoidCase）と降下・弱始性の議論は WeaklyInitialAndDescent に残す。

## 規約
S 離散。完備化は H⁰(LΛ_p)（U4）。

## 使われ方
A5-4（弱始対象・降下）、A1-5（`polyRootAlgebra`）、A5-3（Lemma 8.6 の T → T_∞）、A6-1（Lemma 8.8 の前段の後の根添加）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-! ## (1) S̃（弱始対象の土台） -/

/-- 概要：一段：S_1 = (S⟨X_s, Y_s : s ∈ S⟩/(s − X_s^p − pY_s))^∧（全元に p 乗根を mod p で添加）。
方針：`MvPolynomial (S ⊕ S) S` の商の p 進完備化（H⁰、U4）。
規約：関手的（S の射で変数を送る）。
使われ方：`rootClosure`。 -/
def rootAdjunctionStep : Type u := sorry

/-- 概要：S̃ := (colim_k S_k)^∧（ω 段、D51）。
方針：段の余極限の p 進完備化。
規約：R 代数、S → S̃。
使われ方：弱始対象。 -/
def rootClosure : Type u := sorry
def rootClosureUnit : S →+* rootClosure p R S := sorry

/-- 概要：(i) 延長性：任意の perfectoid T と S → T は S̃ → T に延びる（各段：s ↦ t、y^p ≡ t mod p の y、X_s ↦ y、Y_s ↦ (t − y^p)/p の原像）。
方針：Frobenius 全射（perfectoid）と p 完備性で段ごとに延長し余極限へ。
規約：延長は一意でない（存在だけ）。
使われ方：弱始性。 -/
theorem rootClosure_extends : True := by trivial

/-- 概要：(iii) #S̃ ≤ (#S + ℵ₀)^{ℵ₀} ≤ κ。
方針：各段の濃度評価と完備化の濃度（A0 `cardinal_envelope_le` と同型の議論）。
規約：κ = `cutoff`。
使われ方：κ 側の site の対象になること（D47）。 -/
theorem rootClosure_cardinal_le : True := by trivial

/-- 概要：(iv) S ↦ S̃ は関手的（段ごとに X_a ↦ X_{f(a)}、Y_a ↦ Y_{f(a)}）。
**完備化した filtered 余極限とは可換でない**（W9-II-09：完備化で現れる元に付く独立な Y 変数が有限段から来ない。反例 R = Z_p[p^{1/p^∞}]^∧、S_n = R⟨t_1..t_n⟩、
s = Σ p^j t_j）。旧 `rootClosure_filteredColimit` は撤回。filtered 余極限の段は下の `algebraicRootClosure` を使う。
方針：段ごとの関手性。
規約：—
使われ方：弱始対象の関手性のみ。 -/
theorem rootClosure_functorial : True := by trivial

/-- 概要：G-A5-18：完備化前の代数的な根添加 E(C)：E_0 = C、E_{k+1} = E_k[X_a, Y_a : a ∈ E_k]/(a − X_a^p − pY_a)、E = colim_k E_k（途中で完備化しない）。
通常の環の filtered 余極限と可換。各段は Y 変数上の X のモニック関係で自由な拡大。
方針：`MvPolynomial` の商の余極限。
規約：通常の環。
使われ方：filtered 図式に整合する被覆 E(S_alg)^∧_p。 -/
def algebraicRootClosure (C : Type u) [CommRing C] : Type u := sorry
theorem algebraicRootClosure_filteredColimit : True := by trivial

/-! ## (3) T_∞ と S ⊗̂_T T_∞ -/

/-- 概要：T_∞ = R⟨X_1^{1/p^∞},…,X_r^{1/p^∞}⟩（p 完備化）と T = R⟨X_1,…,X_r⟩ → T_∞。
方針：`MvPolynomial (Fin r × ℕ)` の商の p 進完備化、既存の `CompatibleRootCompletion` の多変数版（要確認）。
規約：—
使われ方：S̃ = S ⊗̂_T T_∞。 -/
def polyRootAlgebra (r : ℕ) : Type u := sorry

/-- 概要：S̃ = S ⊗̂_T T_∞（T → S 全射）と S̃^n = (S̃^{⊗_S n+1})^∧。各 S̃^n は semiperfectoid（S/p の元は R/p 係数の x_i の多項式）。
方針：完備テンソル。
規約：`IsSemiperfectoid`。
使われ方：降下。 -/
def rootCover (r : ℕ) (f : Fin r → S) : Type u := sorry

end SerrePositivity.BhattScholze.Perfectoidization.Derived
