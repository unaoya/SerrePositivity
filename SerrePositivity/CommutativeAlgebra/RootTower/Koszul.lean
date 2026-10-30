module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.RootTower.Restriction
public import SerrePositivity.CommutativeAlgebra.Koszul.FiniteLength
public import SerrePositivity.PerfectComplex.NormalizedLengthComap

/-! # 完備化した根の塔上の Koszul 冪ねじれ

有限局所包含に対する極大イデアルの像を比較し、
任意のパラメータ系の Koszul ホモロジーに一様な消去冪を供給する。
長さの消滅・加法性・perfectoid 性はこの証明に含めない。
-/

@[expose] public section
universe u
open IsLocalRing
namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)
    [IsLocalRing A]
    (D : Type u) [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (C : Type u) [CommRing C] [Algebra A C] [Algebra D C]
    [Algebra (Tower A t p) C] [Algebra (CompletedTower A t p) C]
    [IsScalarTower A D C] [IsScalarTower A (Tower A t p) C]
    [IsScalarTower A (CompletedTower A t p) C]
    [IsScalarTower (Tower A t p) (CompletedTower A t p) C]

include hinj in
omit [Algebra (Tower A t p) C] [IsScalarTower A (Tower A t p) C]
  [IsScalarTower (Tower A t p) (CompletedTower A t p) C] in
/-- `m_A` の完備化・`C` での像は `m_D C` に含まれる。 -/
theorem completedTowerMaxIdeal_map_le :
    (completedTowerMaxIdeal A t p).map (algebraMap (CompletedTower A t p) C) ≤
      (maximalIdeal D).map (algebraMap D C) := by
  dsimp only [completedTowerMaxIdeal]
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A D C,
    ← Ideal.map_map]
  exact Ideal.map_mono (maximalIdeal_map_le_of_finite_of_injective A D hinj)

include hinj in
omit [Algebra (Tower A t p) C] [IsScalarTower A (Tower A t p) C]
  [IsScalarTower (Tower A t p) (CompletedTower A t p) C] in
/-- パラメータ系の Koszul ホモロジーは、完備化した塔の `m_A` の冪で消える。
任意の係数拡大に共通する消去冪と `m_A D ⊆ m_D` から従う。 -/
theorem isPowTorsion_completedTower_koszul [IsNoetherianRing D]
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (i : ℕ) :
    letI := Module.compHom (koszulHomologySelf (fun j ↦ algebraMap D C (z j)) i)
      (algebraMap (CompletedTower A t p) C)
    IsPowTorsion (completedTowerMaxIdeal A t p)
      (koszulHomologySelf (fun j ↦ algebraMap D C (z j)) i) := by
  apply IsPowTorsion.comap _ (completedTowerMaxIdeal_map_le A t p D hinj C)
  obtain ⟨N, hN⟩ := exists_pow_annihilates_koszul_baseChange D z hz
  refine ⟨N, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator]
  intro a ha
  have hann := hN C (algebraMap D C) (-(i : ℤ))
  rw [Ideal.map_pow] at hann
  exact hann ha


end SerrePositivity.Section2
