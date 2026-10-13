module

public import SerrePositivity.CommutativeAlgebra.RootTower.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # 有限局所包含と根の塔の拡大イデアル

有限で単射な局所環の写像で極大イデアルの像が包含されることと、
根の塔を経由する両立した作用で同じ包含が成り立つことを証明する。
長さの引用や perfectoid 性は使わない。既存の宣言名を保持する。
-/

@[expose] public section
universe u
open IsLocalRing
namespace SerrePositivity.Section2

/-- 局所環 `A` 上有限な局所環 `D` で `A → D` が単射なら `m_A D ⊆ m_D`（`A → D` は整拡大なので
局所準同型）。 -/
lemma maximalIdeal_map_le_of_finite_of_injective (A D : Type u) [CommRing A] [IsLocalRing A]
    [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D)) :
    (maximalIdeal A).map (algebraMap A D) ≤ maximalIdeal D := by
  have : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hinj
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact (mem_nonunits_iff.mp ((mem_maximalIdeal a).mp ha)) (IsLocalHom.map_nonunit a hu)

variable (A D : Type u) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D] [Algebra A D]
  [Module.Finite A D] (hinj : Function.Injective (algebraMap A D)) {h : ℕ} (t : Fin h → A) (p : ℕ)
  (C : Type u) [CommRing C] [Algebra A C] [Algebra D C] [Algebra (Tower A t p) C]
  [IsScalarTower A D C] [IsScalarTower A (Tower A t p) C]

include hinj in
/-- `m_A C ≤ 𝔡 C`：`m_A Λ` の `C` での像は `m_D C` に入る。 -/
lemma towerMaxIdeal_map_le :
    (towerMaxIdeal A t p).map (algebraMap (Tower A t p) C) ≤
      (maximalIdeal D).map (algebraMap D C) := by
  dsimp only [towerMaxIdeal]
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A D C,
    ← Ideal.map_map]
  exact Ideal.map_mono (maximalIdeal_map_le_of_finite_of_injective A D hinj)

end SerrePositivity.Section2
