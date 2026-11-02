-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.UniversalProperty（仮。原典 Cor 8.14 と E3 の欄 universal）
-- 設計書：formalization-plans/bhatt-scholze/a7-design.md §2.3、単位 A7-2。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Perfectoidization.Interface
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
-- 本ファイルは drafts/A7/AnimatedPerfectoidization.lean、drafts/A4/{Perfectoidization,InterfaceFields}.lean、drafts/A5/{PerfectSiteComparison,SemiperfectoidCase}.lean を import する。

/-!
# 離散な場合の普遍性（BS 著者版 Cor 8.14）と E3 の欄 `universal`

## 概要
S_perfd が離散なら S_perfd は perfectoid 環で、S → S_perfd は perfectoid 環への普遍な写像（`IsPerfectoidization`）。E3 の欄は任意の離散 S
（非完備も）について `IsDiscrete R (e3Perfd S) → IsPerfectoidization p (unit S)` で、S^∧ 経由（D41）。

## 方針
芯 G-A7-5（A5-2 と共有）：S_perfd 離散 ⇒ Δ_perf 離散（d 進 Nakayama）⇒ 完全 p 完備 δ 環（A4）⇒ 完全 prism ⇒ S_perfd perfectoid（Thm 3.10）。
普遍性：存在は比較写像の脚（A5-1）、一意性は原典：g_1, g_2 が S 上で一致 ⇒ η = (g_1, g_2) : X := S_perfd ⊗̂^L_S S_perfd → S′ は
X_perfd ≃ S_perfd（Prop 8.13、T perfectoid ⇒ T_perfd = T）を通り乗法で因数分解 ⇒ g_1 = g_2。

## 規約
S 離散。離散な環の間の animated／E∞ 代数の射は環準同型（`discreteToAnimated_fullyFaithful`）。

## 使われ方
`PerfectoidizationInterfaceCAlg.universal`（A9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-! ## G-A7-3：perfectoid の perfd -/

/-- 概要：T perfectoid（R 代数）なら T → T_perfd は同値（CAlg_R）、よって (T_perfd)_perfd ≃ T_perfd（T_perfd perfectoid のとき）。
方針：T は semiperfectoid で普遍 perfectoid 化は T 自身、A5-2 `perfectoidization_semiperfectoid_iso`。
規約：—
使われ方：Cor 8.14 の一意性。 -/
theorem perfectoidization_of_perfectoid (T : Type u) [CommRing T] [Algebra R T] (hT : IsIntegralPerfectoid T p) : True := by trivial

/-! ## G-A7-5：芯（A5-2 と共有） -/

/-- 概要：S_perfd が離散なら Δ_{S/A,perf} も離散（d 進 Nakayama：d 完備で mod d が離散）。
方針：DerivedGeneral/Truncation。
規約：`IsDiscrete`。
使われ方：芯。 -/
theorem prismaticPerfection_discrete_of_perfectoidization_discrete (h : True) : True := by trivial

/-- 概要：S_perfd 離散 ⇒ (H⁰(Δ_perf), (d)) は完全 prism（A4 `prismaticPerfection_h0_perfectDelta`・`prismaticPerfectionPrism`）。
方針：上と A4。
規約：`OrientedPrism`。
使われ方：perfectoid 性。 -/
theorem perfectoidization_perfectPrism_of_discrete (h : True) : True := by trivial

/-- 概要：Cor 8.14 前半：S_perfd 離散 ⇒ S_perfd（環として H⁰）は perfectoid（完全 prism の商、`quotient_isIntegralPerfectoid`）。
方針：上。A5-2 の `perfectoidization_isIntegralPerfectoid_of_semiperfectoid` はこれに連結性を前置したもの。
規約：`IsIntegralPerfectoid (H⁰) p`。
使われ方：`universal` の第一成分。 -/
theorem perfectoidization_isIntegralPerfectoid_of_discrete (h : True) : True := by trivial

/-! ## Cor 8.14 後半：普遍性 -/

/-- 概要：存在：perfectoid S′ と S → S′ に対し S_perfd → S′（S の下）：比較写像の脚 Δ_{S,perf} → B_{S′}（A5-1 `perfectionLeg`）の mod d。
方針：A5-1。
規約：環準同型（両者離散）。
使われ方：`IsPerfectoidization` の存在部分。 -/
theorem exists_extension_of_perfectoid : True := by trivial

/-- 概要：X := S_perfd ⊗̂^L_S S_perfd（`CompleteAnimatedAlgebra`）の perfd は S_perfd：Prop 8.13（S_1 = S_2 = S_perfd、S_3 = S）と
(S_perfd)_perfd ≃ S_perfd（`perfectoidization_of_perfectoid`）。単位 X → X_perfd とこの同値の合成は乗法 m : X → S_perfd（紙 3）。
方針：A7-1 `perfectoidization_relativeTensor`。
規約：—
使われ方：一意性。 -/
theorem selfTensor_perfectoidization_eq : True := by trivial
theorem selfTensor_unit_eq_mul : True := by trivial

/-- 概要：一意性：g_1, g_2 : S_perfd → S′（S′ perfectoid）が S 上で一致すれば g_1 = g_2。
方針：η := (g_1, g_2) : X → S′（押し出しの普遍性、G-A7-6）。S′ perfectoid なので η は X → X_perfd → S′_perfd ≃ S′ を通り、`selfTensor_unit_eq_mul` で
η = g ∘ m。g_i = η ∘ i_i = g。離散な標的なので π_0 Map = Hom（`discreteToAnimated_fullyFaithful`）。
規約：—
使われ方：`IsPerfectoidization` の一意性部分。 -/
theorem extension_unique_of_perfectoid : True := by trivial

/-- 概要：Cor 8.14：S_perfd 離散 ⇒ `IsPerfectoidization p (S → S_perfd)`。
方針：`perfectoidization_isIntegralPerfectoid_of_discrete`、`exists_extension_of_perfectoid`、`extension_unique_of_perfectoid`。
規約：S は導来 p 完備な離散 R 代数。
使われ方：`e3Universal`。 -/
theorem perfectoidization_isPerfectoidization_of_discrete (h : True) : True := by trivial

/-! ## E3 の欄 -/

/-- 概要：E3 の `universal`：任意の離散 S について、`e3Perfd S` が離散なら `IsPerfectoidization p (e3H0RingData.unit.app S)`。
方針：S^∧ に Cor 8.14（`e3Perfd_of_complete`・`e3Unit_of_complete`・`e3H0_of_complete`、A4-3）。perfectoid 環は p 完備なので S → T は S^∧ → T を
一意に通る（`completionRing` の普遍性、Interface.lean:237、G-A7-7）。
規約：`PerfectoidizationInterfaceCAlg.universal` の型そのまま。
使われ方：A9。 -/
theorem e3Universal (S : A_R R) (hS : IsDiscrete R ((e3Perfd p R).app _ (nerveVertex S))) :
    IsPerfectoidization p ((e3H0RingData p R).unit.app S).right.hom := by
  sorry -- Cor 8.14（A7-1・A7-2）を待つ

end SerrePositivity.BhattScholze.Perfectoidization.Derived
