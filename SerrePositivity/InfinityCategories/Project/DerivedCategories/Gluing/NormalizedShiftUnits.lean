module
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-! 正規化した標準シフト射影の閉斉次逆元と、通常順の両単位関係。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 正規化した射影と通常順で互いに逆になる次数 −n の同じ包含。 -/
def dgGluingNormalizedShiftIn (n : ℤ) (U : RightModule R D) :
    (moduleHom R D U (shiftModule n U)).X (-n) :=
  (moduleShiftNormalizationExponent n).negOnePow • moduleShiftInElement R D n U

lemma dgGluingNormalizedShiftIn_π (n : ℤ) (U : RightModule R D) (x : D) :
    (moduleHomπ R D U (shiftModule n U) x).f (-n) (dgGluingNormalizedShiftIn R D n U) =
      (Cochain.ofHom (𝟙 (U.obj (op x)))).rightShift n (-n) (neg_add_cancel n) := by
  simp only [dgGluingNormalizedShiftIn, Units.smul_def, map_zsmul,
    moduleShiftInElement_π]
  change (moduleShiftNormalizationExponent n).negOnePow •
    ((moduleShiftNormalizationExponent n).negOnePow •
      (Cochain.ofHom (𝟙 (U.obj (op x)))).rightShift n (-n) (neg_add_cancel n)) = _
  rw [smul_smul, Int.units_mul_self, one_smul]

lemma dgGluingNormalizedShiftIn_v (n : ℤ) (U : RightModule R D) (x : D) (i : ℤ) :
    (((moduleHomπ R D U (shiftModule n U) x).f (-n)
      (dgGluingNormalizedShiftIn R D n U)).v (i + n) i (by omega)) = 𝟙 _ := by
  rw [dgGluingNormalizedShiftIn_π,
    Cochain.rightShift_v _ n (-n) (neg_add_cancel n) (i + n) i (by omega)
      (i + n) (add_zero _)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.id_comp]

lemma dgGluingNormalizedShiftIn_closed (n : ℤ) (U : RightModule R D) :
    (moduleHom R D U (shiftModule n U)).d (-n) (-n + 1)
      (dgGluingNormalizedShiftIn R D n U) = 0 := by
  simp only [dgGluingNormalizedShiftIn, Units.smul_def, map_zsmul,
    moduleShiftInElement_d, zsmul_zero]

lemma dgGluingNormalizedShiftOutIn (n : ℤ) (U : RightModule R D) :
    compose R (dgGluingNormalizedShiftIn R D n U) (normalizedModuleShiftOut R D n U)
      (add_neg_cancel n) = (unitElement R (shiftModule n U)).val := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleHomCompose_π]
  have h := congrArg (fun z => (moduleHomπ R D (shiftModule n U) (shiftModule n U) x).f 0 z)
    (moduleShiftOutIn R D n U)
  rw [moduleHomCompose_π] at h
  simp only [normalizedModuleShiftOut, dgGluingNormalizedShiftIn, Units.smul_def, map_zsmul]
  simp only [← Units.smul_def]
  erw [Cochain.units_smul_comp, Cochain.comp_units_smul]
  rw [smul_smul, Int.units_mul_self, one_smul]
  exact h

lemma dgGluingNormalizedShiftInOut (n : ℤ) (U : RightModule R D) :
    compose R (normalizedModuleShiftOut R D n U) (dgGluingNormalizedShiftIn R D n U)
      (neg_add_cancel n) = (unitElement R U).val := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleHomCompose_π]
  have h := congrArg (fun z => (moduleHomπ R D U U x).f 0 z) (moduleShiftInOut R D n U)
  rw [moduleHomCompose_π] at h
  simp only [normalizedModuleShiftOut, dgGluingNormalizedShiftIn, Units.smul_def, map_zsmul]
  simp only [← Units.smul_def]
  erw [Cochain.units_smul_comp, Cochain.comp_units_smul]
  rw [smul_smul, Int.units_mul_self, one_smul]
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
