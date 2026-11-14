module

public import SerrePositivity.EInfinity.PowerOperation.BoundedAcyclicHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# 係数側の有界性による完全周期 Hom の非輪状性

DAG XIII Construction 2.2.6 の完全入力の模型比較に用いる補助。
始域は各項の射影性だけを仮定し、非輪状な値域の上有界性を明示する。
したがって、非有界な周期解像度の K 射影性を主張していない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- 線形 Hom の係数計算に用いる、一般のアーベル圏の非輪状性のシフト保存。 -/
lemma boundedCoefficientAcyclic_shift {M : CochainComplex C ℤ} (hM : M.Acyclic) (n : ℤ) :
    (M⟦n⟧).Acyclic := by
  intro i
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ i).mpr
    (((CochainComplex.ShiftSequence.shiftIso C n i (n + i) rfl).app M).isZero_iff.mpr
      (hM (n + i)).isZero_homology)

/-- 射影的な各項から上有界な非輪状複体への全 Hom 複体は非輪状。 -/
lemma linearHomComplex_acyclic_boundedAbove (R : Type w) [CommRing R] [Linear R C]
    (P M : CochainComplex C ℤ) (d : ℤ) [M.IsStrictlyLE d]
    [∀ n, Projective (P.X n)] (hM : M.Acyclic) :
    (linearHomComplex R P M).Acyclic := by
  intro n
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ n).mpr
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hzero (c : CohomologyClass P M n) : c = 0 := by
    apply (CohomologyClass.toHom_bijective P M n).1
    rw [map_zero]
    obtain ⟨f, hf⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective
      (CohomologyClass.toHom c)
    rw [← hf, HomotopyCategory.quotient_map_eq_zero_iff]
    have : (M⟦n⟧).IsStrictlyLE (d - n) := M.isStrictlyLE_shift d n (d - n) (by omega)
    exact homotopyZero_to_acyclic_boundedAbove f (d - n) (boundedCoefficientAcyclic_shift hM n)
  constructor
  intro x y
  apply (HomComplex.homologyLinearEquiv R P M n).injective
  exact (hzero _).trans (hzero _).symm

end SerrePositivity.EInfinity.PowerOperation
