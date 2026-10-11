module

public import SerrePositivity.CommutativeAlgebra.ReesModule
public import SerrePositivity.CommutativeAlgebra.GradedKoszulHomology

@[expose] public noncomputable section
universe u

namespace SerrePositivity.GradedKoszul
open SerrePositivity.HilbertSamuel SerrePositivity.HilbertSerre
open scoped DirectSum
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The homogeneous Rees monomials of coefficient degree `n`. -/
def reesModuleGrade (n : ℕ) : Submodule R (ReesModule R I M) :=
  (reesSingle R I M n).range

theorem isInternal_reesModuleGrade : DirectSum.IsInternal (reesModuleGrade R I M) := by
  let p (n : ℕ) : ReesModule R I M →ₗ[R] ReesModule R I M :=
    (reesSingle R I M n).comp (reesCoefficient R I M n)
  apply isInternal_of_projections (reesModuleGrade R I M) p
  · intro n x
    obtain ⟨a, ha⟩ := x.2
    rw [← ha]
    change reesSingle R I M n (reesCoefficient R I M n (reesSingle R I M n a)) = _
    rw [reesCoefficient_reesSingle]
  · intro n k hkn x
    obtain ⟨a, ha⟩ := x.2
    rw [← ha]
    change reesSingle R I M n (reesCoefficient R I M n (reesSingle R I M k a)) = 0
    have hzero : reesCoefficient R I M n (reesSingle R I M k a) = 0 := by
      apply Subtype.ext
      change (Finsupp.single k (a : M)) n = 0
      exact Finsupp.single_eq_of_ne (Ne.symm hkn)
    rw [hzero, map_zero]
  · apply top_unique
    intro x _
    rw [reesModule_as_sum R I M x]
    apply Submodule.sum_mem
    intro n _
    exact (le_iSup (reesModuleGrade R I M) n) ⟨_, rfl⟩


end SerrePositivity.GradedKoszul
