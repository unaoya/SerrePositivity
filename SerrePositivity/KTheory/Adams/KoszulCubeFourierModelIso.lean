module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierModelInverse

/-! # The equivariant four-shift Fourier chain isomorphism for a Koszul cube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

instance oneKoszulCubeFourierModelMap_f_isIso (a t : R) (ht : t ^ 2 + t + 1 = 0)
    (n : ℤ) : IsIso ((oneKoszulCubeFourierModelMap a t ht).f n) := by
  by_cases hnZero : n = 0
  · subst n
    exact ⟨⟨oneKoszulCubeFourierModelInverseZero a t,
      oneKoszulCubeFourierModelMap_inverseZero a t ht,
      oneKoszulCubeFourierModelInverseZero_map a t ht⟩⟩
  by_cases hnNegOne : n = -1
  · subst n
    exact ⟨⟨oneKoszulCubeFourierModelInverseNegOne a t,
      oneKoszulCubeFourierModelMap_inverseNegOne a t ht,
      oneKoszulCubeFourierModelInverseNegOne_map a t ht⟩⟩
  by_cases hnNegTwo : n = -2
  · subst n
    exact ⟨⟨oneKoszulCubeFourierModelInverseNegTwo a t,
      oneKoszulCubeFourierModelMap_inverseNegTwo a t ht,
      oneKoszulCubeFourierModelInverseNegTwo_map a t ht⟩⟩
  by_cases hnNegThree : n = -3
  · subst n
    exact ⟨⟨oneKoszulCubeFourierModelInverseNegThree a t,
      oneKoszulCubeFourierModelMap_inverseNegThree a t ht,
      oneKoszulCubeFourierModelInverseNegThree_map a t ht⟩⟩
  have hn : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0 := by omega
  have hD := oneKoszulCubeFourierModel_isZero_X_other a n hn
  have hK := oneKoszulCube_isZero_X_other a n hn
  rw [hD.eq_of_src ((oneKoszulCubeFourierModelMap a t ht).f n) 0]
  exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨hD, hK⟩

instance oneKoszulCubeFourierModelMap_isIso (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    IsIso (oneKoszulCubeFourierModelMap a t ht) :=
  HomologicalComplex.Hom.isIso_of_components _

def oneKoszulCubeFourierModelIso (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModel a ≅ tensorCube (oneKoszulComplex a) :=
  asIso (oneKoszulCubeFourierModelMap a t ht)

@[simp]
lemma oneKoszulCubeFourierModelIso_hom (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelIso a t ht).hom = oneKoszulCubeFourierModelMap a t ht := rfl

lemma oneKoszulCubeFourierModelIso_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelIso a t ht).hom ≫ tensorCubeRotation (oneKoszulComplex a) =
      (oneKoszulCubeFourierModelAction a t ht).map ≫
        (oneKoszulCubeFourierModelIso a t ht).hom :=
  oneKoszulCubeFourierModelMap_rotation a t ht

end Adams
end SerrePositivity
