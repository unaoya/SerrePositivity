module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierEmbeddings
public import SerrePositivity.PerfectComplex.BiproductPerfect
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.PerfectComplex.Eigen.Cubic

/-! # The four-shift Fourier model and its equivariant map to the Koszul cube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulCubeFourierModel (a : R) :=
  oneKoszulComplex a ⊞
    (oneKoszulShiftOne a ⊞ (oneKoszulShiftOne a ⊞ oneKoszulShiftTwo a))

def oneKoszulCubeFourierModelRotation (a t : R) :
    oneKoszulCubeFourierModel a ⟶ oneKoszulCubeFourierModel a :=
  biprod.map (𝟙 _) (biprod.map (t • 𝟙 _) (biprod.map (t ^ 2 • 𝟙 _) (𝟙 _)))

/-- The four scalar actions, using character zero on the two even shifts. -/
def oneKoszulCubeFourierScalarAction (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    CochainCubicAction (oneKoszulCubeFourierModel a) :=
  let action (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : Fin 3) :=
    CochainCubicAction.characterScalar K t (cube_eq_one_of_cubic_relation t ht) j
  (action (oneKoszulComplex a) 0).biprod
    ((action (oneKoszulShiftOne a) 1).biprod
      ((action (oneKoszulShiftOne a) 2).biprod (action (oneKoszulShiftTwo a) 0)))

lemma oneKoszulCubeFourierModelRotation_cube (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelRotation a t ≫ oneKoszulCubeFourierModelRotation a t ≫
      oneKoszulCubeFourierModelRotation a t = 𝟙 _ := by
  simpa only [oneKoszulCubeFourierScalarAction, CochainCubicAction.biprod_map,
    CochainCubicAction.characterScalar_map, cubicCharacter, Fin.val_zero, Fin.val_one,
    Fin.val_two, pow_zero, pow_one, one_smul, oneKoszulCubeFourierModelRotation] using
    (oneKoszulCubeFourierScalarAction a t ht).cube

def oneKoszulCubeFourierModelAction (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    CochainCubicAction (oneKoszulCubeFourierModel a) where
  map := oneKoszulCubeFourierModelRotation a t
  cube := oneKoszulCubeFourierModelRotation_cube a t ht

lemma oneKoszulCubeFourierModel_perfect (a : R) :
    strictlyPerfectComplex R (oneKoszulCubeFourierModel a) :=
  strictlyPerfectComplex_biprod (oneKoszulComplex_perfect a)
    (strictlyPerfectComplex_biprod (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1)
      (strictlyPerfectComplex_biprod (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1)
        (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 2)))

lemma oneKoszulCubeFourierModel_support (a : R) :
    HasHomologySupportOn (oneKoszulSupport a) (oneKoszulCubeFourierModel a) :=
  (oneKoszulComplex_support a).biprod
    (((oneKoszulComplex_support a).shift 1).biprod
      (((oneKoszulComplex_support a).shift 1).biprod ((oneKoszulComplex_support a).shift 2)))

lemma oneKoszulCubeFourierModel_isZero_X_other (a : R) (n : ℤ)
    (hn : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0) :
    IsZero ((oneKoszulCubeFourierModel a).X n) := by
  have hz {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
      (hP : IsZero (P.X n)) (hQ : IsZero (Q.X n)) : IsZero ((P ⊞ Q).X n) :=
    ((biprod_isZero_iff _ _).mpr ⟨hP, hQ⟩).of_iso (biprodXIso P Q n)
  exact hz (oneKoszul_isZero_X_other a n (by omega))
    (hz (oneKoszulShiftOne_isZero_X_other a n (by omega))
      (hz (oneKoszulShiftOne_isZero_X_other a n (by omega))
        (oneKoszulShiftTwo_isZero_X_other a n (by omega))))

variable [Invertible (3 : R)]

def oneKoszulCubeFourierModelMap (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModel a ⟶ tensorCube (oneKoszulComplex a) :=
  biprod.desc (oneKoszulCubeFourierZeroEmbedding a)
    (biprod.desc (oneKoszulCubeFourierOneEmbedding a t ht)
      (biprod.desc (oneKoszulCubeFourierTwoEmbedding a t ht)
        (oneKoszulCubeFourierTopEmbedding a t)))

lemma oneKoszulCubeFourierModelMap_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelMap a t ht ≫ tensorCubeRotation (oneKoszulComplex a) =
      oneKoszulCubeFourierModelRotation a t ≫ oneKoszulCubeFourierModelMap a t ht := by
  apply biprod.hom_ext'
  · simp [oneKoszulCubeFourierModelMap, oneKoszulCubeFourierModelRotation,
      oneKoszulCubeFourierZeroEmbedding_rotation]
  · apply biprod.hom_ext'
    · simp [oneKoszulCubeFourierModelMap, oneKoszulCubeFourierModelRotation,
        Linear.smul_comp, oneKoszulCubeFourierOneEmbedding_rotation a t ht]
    · apply biprod.hom_ext'
      · simp [oneKoszulCubeFourierModelMap, oneKoszulCubeFourierModelRotation,
          Linear.smul_comp, oneKoszulCubeFourierTwoEmbedding_rotation a t ht]
      · simp [oneKoszulCubeFourierModelMap, oneKoszulCubeFourierModelRotation,
          oneKoszulCubeFourierTopEmbedding_rotation]

end Adams
end SerrePositivity
