-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.UniversalProperty（仮。原典 Cor 8.14 と E3 の欄 universal）
-- 設計書：formalization-plans/bhatt-scholze/a7-design.md §2.3、単位 A7-2。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Perfectoidization.Interface
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
-- 本ファイルは drafts/A7/{AnimatedDomain,DiscreteCore,AnimatedPerfectoidization}.lean、drafts/A4/{Perfectoidization,InterfaceFields}.lean、drafts/A5/{PerfectSiteComparison,SemiperfectoidCase}.lean を import する。
-- G-A7-5 の芯は drafts/A7/DiscreteCore.lean に切り出した（W9-II-24：A5 が import するので本ファイルには置けない）。

/-!
# 離散な場合の普遍性（BS 著者版 Cor 8.14）と E3 の欄 `universal`

## 概要
S_perfd が離散なら S_perfd は perfectoid 環で、S → S_perfd は perfectoid 環への普遍な写像（`IsPerfectoidization`）。E3 の欄は任意の離散 S
（非完備も）について `IsDiscrete R (e3Perfd S) → IsPerfectoidization p (unit S)` で、S^∧ 経由（D41）。

## 方針
芯 G-A7-5（A5-2 と共有、drafts/A7/DiscreteCore.lean）：S_perfd 離散 ⇒ Δ_perf 離散（d 進 Nakayama）⇒ 完全 p 完備 δ 環（A4）⇒ 完全 prism ⇒ S_perfd perfectoid（Thm 3.10）。
普遍性：存在は比較写像の脚（A5-1）、一意性は原典：g_1, g_2 が S 上で一致 ⇒ η = (g_1, g_2) : X := S_perfd ⊗̂^L_S S_perfd → S′ は
X_perfd ≃ S_perfd（Prop 8.13、T perfectoid ⇒ T_perfd = T）を通り乗法で因数分解 ⇒ g_1 = g_2。乗法との一致には単位の整合性 F(η_S) = η_P（G-A7-8、
A5 の極限の脚から。W9-II-23：単位の自然性だけでは不足）を先に示す。

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

/-! ## Cor 8.14 後半：普遍性 -/

/-- 概要：存在：perfectoid S′ と S → S′ に対し S_perfd → S′（S の下）：比較写像の脚 Δ_{S,perf} → B_{S′}（A5-1 `perfectionComparisonLeg`）の mod d。
方針：A5-1。
規約：環準同型（両者離散）。
使われ方：`IsPerfectoidization` の存在部分。 -/
theorem exists_extension_of_perfectoid : True := by trivial

/-- 概要：G-A7-8（W9-II-23）：単位の整合性。P := S_perfd が離散（よって perfectoid、DiscreteCore）のとき F(η_S) = η_P : P → P_perfd（F = perfd）。
方針：A5-1 の極限表示 P = lim_{Perfd_{S/}} O の脚 λ_f : P → T（f : S → T）。f = η_S の脚を q : P → P とすると、任意の f について λ_f は添字圏の射
(P, η_S) → (T, f) なので錐の可換性から λ_f ∘ q = λ_f、P・T は離散で脚は射を識別する（極限は環の極限）ので q = id_P。極限比較の S に関する自然性と η_P の可逆性
（`perfectoidization_of_perfectoid`）から η_P^{-1} ∘ F(η_S) = q = id_P。Cor 8.14 の一意性は使わない（循環なし）。単位の自然性だけでは「S 上で一致」までしか出ない。
規約：—
使われ方：`selfTensor_unit_eq_mul`。 -/
theorem perfectoidization_map_unit_eq_unit (h : True) : True := by trivial

/-- 概要：X := S_perfd ⊗̂^L_S S_perfd（`CompleteAnimatedAlgebra`）の perfd は S_perfd：Prop 8.13（S_1 = S_2 = S_perfd、S_3 = S）と
(S_perfd)_perfd ≃ S_perfd（`perfectoidization_of_perfectoid`）。単位 X → X_perfd とこの同値の合成は乗法 m : X → S_perfd（紙 3）。
方針（W9-II-23）：Prop 8.13 の比較 F(P) ⊗̂_{F(S)} F(P) → F(X) の二つの脚は F(i_1)・F(i_2)。`perfectoidization_map_unit_eq_unit` と η_P の逆で左辺を P ⊗̂_P P ≃ P と
同一視し、逆向きを e : F(X) → P とすると、単位の自然性から e ∘ η_X ∘ i_j = e ∘ F(i_j) ∘ η_P = id_P、押し出しの普遍性（G-A7-6）で e ∘ η_X = m。
A7-1 `perfectoidization_relativeTensor`。
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
