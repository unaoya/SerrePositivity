module

public import SerrePositivity.HomologicalAlgebra.FlatBaseChange
public import SerrePositivity.Paper.Section2.TowerDescent

/-! # 有限段から得た Koszul ホモロジーの正規化長さ

`B = Λ ⊗_{A_n} T` における Koszul ホモロジーは、`T` 上のホモロジーの
`A_n → Λ` に沿う係数拡大である。有限段で有限長なら、正規化長さは
その通常の長さを `p^(nh)` で割った値になる。
-/

public section

universe u

namespace SerrePositivity.Section2

open IsLocalRing
open scoped ENNReal

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A) (n : ℕ)
    (T B : Type u) [CommRing T] [CommRing B]
    [Algebra (TowerStage A t p n) T] [Algebra (Tower A t p) B] [Algebra T B]
    [Algebra (TowerStage A t p n) B]
    [IsScalarTower (TowerStage A t p n) (Tower A t p) B]
    [IsScalarTower (TowerStage A t p n) T B]
    [Algebra.IsPushout (TowerStage A t p n) (Tower A t p) T B]

include ht in
/-- 有限段から係数拡大された Koszul ホモロジーの正規化長さの公式。 -/
theorem towerLengthFun_koszulHomology_of_baseChange {r : ℕ} (x : Fin r → T) (i : ℤ)
    (hfin :
      letI := Module.compHom ((koszulComplex x).homology i)
        (algebraMap (TowerStage A t p n) T)
      IsFiniteLength (TowerStage A t p n) ((koszulComplex x).homology i)) :
    letI := Module.compHom ((koszulComplex x).homology i)
      (algebraMap (TowerStage A t p n) T)
    letI := Module.compHom ((koszulComplex (algebraMap T B ∘ x)).homology i)
      (algebraMap (Tower A t p) B)
    towerLengthFun A t p ((koszulComplex (algebraMap T B ∘ x)).homology i) =
      (Module.length (TowerStage A t p n) ((koszulComplex x).homology i) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  let : Module (TowerStage A t p n) ((koszulComplex x).homology i) :=
    Module.compHom _ (algebraMap (TowerStage A t p n) T)
  let : Module (Tower A t p) ((koszulComplex (algebraMap T B ∘ x)).homology i) :=
    Module.compHom _ (algebraMap (Tower A t p) B)
  let := flat_tower A t p n
  rw [towerLengthFun_congr
    (pushoutKoszulHomologyEquiv (TowerStage A t p n) (Tower A t p) T B x i)]
  exact towerLengthFun_tensor_of_finiteLength A t p ht n _ hfin

include ht in
omit [IsNoetherianRing A] in
/-- 同じ有限長性は、係数拡大後のホモロジーが `m_A Λ` の冪で消えることも与える。 -/
theorem isPowTorsion_koszulHomology_of_baseChange {r : ℕ} (x : Fin r → T) (i : ℤ)
    (hfin :
      letI := Module.compHom ((koszulComplex x).homology i)
        (algebraMap (TowerStage A t p n) T)
      IsFiniteLength (TowerStage A t p n) ((koszulComplex x).homology i)) :
    letI := Module.compHom ((koszulComplex (algebraMap T B ∘ x)).homology i)
      (algebraMap (Tower A t p) B)
    IsPowTorsion (towerMaxIdeal A t p)
      ((koszulComplex (algebraMap T B ∘ x)).homology i) := by
  let : Module (Tower A t p) ((koszulComplex (algebraMap T B ∘ x)).homology i) :=
    Module.compHom _ (algebraMap (Tower A t p) B)
  let := flat_tower A t p n
  let := isLocalRing_towerStage A t p ht n
  let M := (koszulComplex x).homology i
  let : Module (TowerStage A t p n) M :=
    Module.compHom M (algebraMap (TowerStage A t p n) T)
  apply IsPowTorsion.of_equiv
    (pushoutKoszulHomologyEquiv (TowerStage A t p n) (Tower A t p) T B x i).symm
  apply isPowTorsion_tower_tensor
  obtain ⟨k, hk⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hfin
  refine ⟨k, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hk ⊢
  exact (pow_le_pow_left'
    (le_of_isMaximal_towerStage A t p ht n (maximalIdeal (TowerStage A t p n))).1 k).trans hk

end SerrePositivity.Section2
