module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierModelIso
public import SerrePositivity.KTheory.Adams.KoszulShiftTwoClass
public import SerrePositivity.PerfectComplex.CubicActionScalarClass
public import SerrePositivity.PerfectComplex.CubicActionBiproductClass

/-! # The weighted character class of the four-shift Koszul Fourier model -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

/-- The four scalar actions, using character zero on the two even shifts. -/
def oneKoszulCubeFourierScalarAction (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    CochainCubicAction (oneKoszulCubeFourierModel a) :=
  (CochainCubicAction.scalar (oneKoszulComplex a) (cubicCharacter t 0)
    (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) 0)).biprod
    ((CochainCubicAction.scalar (oneKoszulShiftOne a) (cubicCharacter t 1)
      (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) 1)).biprod
      ((CochainCubicAction.scalar (oneKoszulShiftOne a) (cubicCharacter t 2)
        (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) 2)).biprod
        (CochainCubicAction.scalar (oneKoszulShiftTwo a) (cubicCharacter t 0)
          (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) 0))))

omit [Invertible (3 : R)] in
lemma oneKoszulCubeFourierModelAction_eq_scalar (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelAction a t ht = oneKoszulCubeFourierScalarAction a t ht := by
  apply CochainCubicAction.ext
  simp [oneKoszulCubeFourierModelAction, oneKoszulCubeFourierModelRotation,
    oneKoszulCubeFourierScalarAction, CochainCubicAction.biprod, CochainCubicAction.scalar,
    cubicCharacter]

lemma oneKoszulCubeFourierModel_weighted_class (E : Type v) [CommRing E]
    (a t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) :
    (oneKoszulCubeFourierModelAction a t ht).weightedK0Class E t ht ζ
      (oneKoszulSupport a) (oneKoszulCubeFourierModel_perfect a)
      (oneKoszulCubeFourierModel_support a) =
      ((2 : E) - ζ - ζ ^ 2) • ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) := by
  let τ0 := CochainCubicAction.scalar (oneKoszulComplex a) (cubicCharacter t 0)
    (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) 0)
  let τ1 := CochainCubicAction.scalar (oneKoszulShiftOne a) (cubicCharacter t 1)
    (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) 1)
  let τ2 := CochainCubicAction.scalar (oneKoszulShiftOne a) (cubicCharacter t 2)
    (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) 2)
  let τ3 := CochainCubicAction.scalar (oneKoszulShiftTwo a) (cubicCharacter t 0)
    (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) 0)
  let hp0 := oneKoszulComplex_perfect a
  let hp1 := strictlyPerfectComplex_shift hp0 1
  let hp2 := strictlyPerfectComplex_shift hp0 2
  let hs0 := oneKoszulComplex_support a
  let hs1 := hs0.shift 1
  let hs2 := hs0.shift 2
  rw [oneKoszulCubeFourierModelAction_eq_scalar]
  change (τ0.biprod (τ1.biprod (τ2.biprod τ3))).weightedK0Class E t ht ζ
    (oneKoszulSupport a) _ _ = _
  rw [CochainCubicAction.weightedK0Class_biprod E τ0 (τ1.biprod (τ2.biprod τ3))
    t ht ζ (oneKoszulSupport a) hp0
    (strictlyPerfectComplex_biprod hp1 (strictlyPerfectComplex_biprod hp1 hp2))
    hs0 (hs1.biprod (hs1.biprod hs2))]
  rw [CochainCubicAction.weightedK0Class_biprod E τ1 (τ2.biprod τ3)
    t ht ζ (oneKoszulSupport a) hp1 (strictlyPerfectComplex_biprod hp1 hp2)
    hs1 (hs1.biprod hs2)]
  rw [CochainCubicAction.weightedK0Class_biprod E τ2 τ3
    t ht ζ (oneKoszulSupport a) hp1 hp2 hs1 hs2]
  rw [CochainCubicAction.weightedK0Class_of_map_eq_scalar E τ0 t ht 0 rfl ζ
    (oneKoszulSupport a) hp0 hs0]
  rw [CochainCubicAction.weightedK0Class_of_map_eq_scalar E τ1 t ht 1 rfl ζ
    (oneKoszulSupport a) hp1 hs1]
  rw [CochainCubicAction.weightedK0Class_of_map_eq_scalar E τ2 t ht 2 rfl ζ
    (oneKoszulSupport a) hp1 hs1]
  rw [CochainCubicAction.weightedK0Class_of_map_eq_scalar E τ3 t ht 0 rfl ζ
    (oneKoszulSupport a) hp2 hs2]
  rw [oneKoszulShiftOne_class a, oneKoszulShiftTwo_class a]
  change cubicCharacter ζ 0 ⊗ₜ[ℤ] oneKoszulClass a +
    (cubicCharacter ζ 1 ⊗ₜ[ℤ] (-oneKoszulClass a) +
      (cubicCharacter ζ 2 ⊗ₜ[ℤ] (-oneKoszulClass a) +
        cubicCharacter ζ 0 ⊗ₜ[ℤ] oneKoszulClass a)) = _
  simp only [cubicCharacter, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    tmul_neg, sub_smul, two_smul, smul_tmul', smul_eq_mul, mul_one]
  abel

end Adams
end SerrePositivity
