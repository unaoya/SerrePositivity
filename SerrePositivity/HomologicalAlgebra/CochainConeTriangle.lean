module
public import SerrePositivity.HomologicalAlgebra.CochainConeCoordinates
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Components of the mapping-cone triangle -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R]
variable {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P')

/-- The connecting map of a cone is minus its shifted first projection. -/
lemma coneTriangle_mor₃_f (n : ℤ) :
    (mappingCone.triangle f).mor₃.f n =
      -((mappingCone.fst f : Cochain (mappingCone f) P 1).v n (n + 1) rfl ≫
        (P.shiftFunctorObjXIso 1 n (n + 1) rfl).inv) := by
  apply mappingCone.ext_from f (n + 1) n rfl
  · simp only [mappingCone.inl_v_triangle_mor₃_f, Preadditive.comp_neg,
      mappingCone.inl_v_fst_v_assoc]
  · simp only [mappingCone.inr_f_triangle_mor₃_f, Preadditive.comp_neg,
      mappingCone.inr_f_fst_v_assoc, zero_comp, neg_zero]

end SerrePositivity
