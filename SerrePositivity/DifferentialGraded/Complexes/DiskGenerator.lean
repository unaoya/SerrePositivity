module
public import SerrePositivity.DifferentialGraded.Complexes.Cells

/-! # diskからの射の逆構成と下の生成元の像 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

lemma complexDiskHomEquiv_symm_generator (K : Complex A) (q : ℤ) (z : K.X q) :
    ((complexDiskHomEquiv A K q).symm z).f q ((complexDiskX₀ A q).inv (1 : A)) = z := by
  have h := (complexDiskHomEquiv A K q).apply_symm_apply z
  rw [complexDiskHomEquiv_apply] at h
  exact h

end SerrePositivity.DifferentialGraded
