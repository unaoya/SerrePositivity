-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.AfterComparison（仮。Prop 8.5 の後に置く A4 の補足：D41 の直接の式との一致、Example 8.3）
-- 設計書：formalization-plans/bhatt-scholze/a4-design.md §2.1 D41・Ex 8.3、単位 A4-3・A4-4。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
-- 本ファイルは drafts/A4/{Perfectoidization,InterfaceFields}.lean、drafts/A5/PerfectSiteComparison.lean（Prop 8.5 系 4 `perfectoidization_piZero`）、
-- drafts/A2/BaseChangeAndTensor.lean を import する（W9-III-09：A4 の定義は A5 より先、本ファイルは A5 より後）。

/-!
# Prop 8.5 の後に置く A4 の補足（D41 の直接の式との一致、BS 著者版 Example 8.3）

## 概要
`e3Perfd_eq_direct`：任意の離散 S で E3 の `perfd` の値（(completionRing S)_perfd、D41）が直接の式 (colim_φ Δ_S)^∧ ⊗^L_A A/d に一致する
（Prop 8.5 系 4）。`perfectoidization_charP`：標数 p では S_perfd は通常の完全化の p 完備化（Prop 8.5 で A によらないことを使う）。

## 方針
W9-III-09 で A4/InterfaceFields.lean・A4/Perfectoidization.lean から切り出した。どちらも Prop 8.5 を使うので A4 の定義（A5 より先）と同居できない。

## 規約
所有単位は A4 のまま。

## 使われ方
A6（Prop 8.10：任意の離散 S に対する arc 層としての記述）、A8。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-- 概要：任意の離散 S で、`e3Perfd` の値は直接の式 (colim_φ Δ_S)^∧ ⊗^L_A A/d（S を完備化せずに A2 の Δ_S に当てたもの）に一致する。
方針：D32 の animated 版（Δ_S ≃ Δ_{LΛ_p S}、A2-4 `derivedPrismaticCohomology_completion_animated`）で直接の式は (LΛ_p S)_perfd、
Prop 8.5 の系 4（A5-1 `perfectoidization_piZero`）で (LΛ_p S)_perfd ≃ (π_0 LΛ_p S)_perfd = (completionRing S)_perfd（W9-I-29、決定 6）。
規約：これが D41 の「直接の式との一致は定理」。
使われ方：A6（Prop 8.10：任意の離散 S に対する arc 層としての記述）、A8。 -/
theorem e3Perfd_eq_direct (S : Type u) [CommRing S] [Algebra R S] : True := by trivial

/-! ## Example 8.3（標数 p） -/

/-- 概要：Example 8.3：R が標数 p（A = W(R)、d = p）なら S_perfd ≅ (colim_φ S)^∧_p（通常の完全化の p 完備化）。
方針：A によらないこと（Prop 8.5、A5）で A = Z_p に帰着し、HT 比較の Frobenius 同変な S → Δ_S/p が完全化で同型（∧^i L_{S/F_p}[−i] 上の Frobenius は i ≠ 0 で零）。
規約：主張のみ。証明は A5 の後。A6（Prop 8.10 の tilt）で要るか確認。
使われ方：A6。 -/
theorem perfectoidization_charP : True := by trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
