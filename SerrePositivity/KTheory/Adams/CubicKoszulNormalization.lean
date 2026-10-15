module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierModelClass
public import SerrePositivity.KTheory.Adams.CyclicThree

/-! # One-element Koszul normalization for the cyclic Adams cube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma tensorCubeClass_oneKoszul_weight (E : Type v) [CommRing E]
    (a t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) :
    tensorCubeClass E t ht ζ (oneKoszulComplex a) (oneKoszulSupport a)
      (oneKoszulComplex_perfect a) (oneKoszulComplex_support a) =
      ((2 : E) - ζ - ζ ^ 2) • ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) := by
  have hf : (oneKoszulCubeFourierModelAction a t ht).map ≫
      (oneKoszulCubeFourierModelIso a t ht).hom =
      (oneKoszulCubeFourierModelIso a t ht).hom ≫ (tensorCubeAction (oneKoszulComplex a)).map :=
    (oneKoszulCubeFourierModelIso_rotation a t ht).symm
  have he := CochainCubicAction.weightedK0Class_eq_of_quasiIso E
    (oneKoszulCubeFourierModelAction a t ht) (tensorCubeAction (oneKoszulComplex a))
    (oneKoszulCubeFourierModelIso a t ht).hom hf t ht ζ (oneKoszulSupport a)
    (oneKoszulCubeFourierModel_perfect a)
    (tensorCube_perfect (oneKoszulComplex a) (oneKoszulComplex_perfect a))
    (oneKoszulCubeFourierModel_support a)
    (tensorCube_support (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))
  exact he.symm.trans (oneKoszulCubeFourierModel_weighted_class E a t ht ζ)

lemma tensorCubeClass_oneKoszul (E : Type v) [CommRing E]
    (a t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    tensorCubeClass E t ht ζ (oneKoszulComplex a) (oneKoszulSupport a)
      (oneKoszulComplex_perfect a) (oneKoszulComplex_support a) =
      (3 : E) • ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) := by
  rw [tensorCubeClass_oneKoszul_weight E a t ht ζ]
  have hc : (2 : E) - ζ - ζ ^ 2 = 3 := by linear_combination -hζ
  rw [hc]

/-- One-element normalization, valid for any scalar a in a commutative ring. -/
lemma cyclicThree_oneKoszul (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) (a : R) :
    cyclicThree E t ht ζ hζ (oneKoszulSupport a) ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) =
      (3 : E) • ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) := by
  rw [oneKoszulClass, cyclicThree_mk_concrete E t ht ζ hζ (oneKoszulSupport a)
    (1 : E) (oneKoszulComplex a) (oneKoszulComplex_perfect a) (oneKoszulComplex_support a),
    one_smul]
  exact tensorCubeClass_oneKoszul E a t ht ζ hζ

end Adams
end SerrePositivity
