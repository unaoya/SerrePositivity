module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfYonedaHomology
public import SerrePositivity.DifferentialGraded.Endomorphism.HomComparisonShift
public import SerrePositivity.DifferentialGraded.Endomorphism.ShiftNaturality

/-! # 射影増強を前合成した全 Hom 比較の shift 計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Hom の源 shift の chain 同型の全次数公式。shift の包含との豊穣合成を保つ。 -/
lemma criterionPerfHomSourceShiftIso_apply (M N : RightModule A D) (s q : ℤ)
    (z : (moduleHom A D (shiftModule s M) N).X q) :
    (moduleHomSourceShiftIso A D M N s).hom.f q z =
      forward A (x := M) (y := shiftModule s M) (z := N)
        (moduleShiftInElement A D s M) z (by omega : -s + q = q + -s) := by
  change (complexShiftIsoOfSumZero A _ _ _ _ _ _).hom.f q z = _
  rw [complexShiftIsoOfSumZero_hom, complexShiftComparison_f]
  rfl

/-- shift の包含は閉零加群射と自然に可換する。 -/
lemma criterionPerfModuleShiftIn_naturality (s : ℤ) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    forward A (x := ForgetEnrichment.to (Complex A) M)
      (y := shiftModule s (ForgetEnrichment.to (Complex A) M))
      (z := shiftModule s (ForgetEnrichment.to (Complex A) N))
      (moduleShiftInElement A D s (ForgetEnrichment.to (Complex A) M))
      (endomorphismClosedElement A D ((moduleShiftFunctor A D s).map f)) (add_zero (-s)) =
    forward A (x := ForgetEnrichment.to (Complex A) M)
      (y := ForgetEnrichment.to (Complex A) N)
      (z := shiftModule s (ForgetEnrichment.to (Complex A) N))
      (endomorphismClosedElement A D f)
      (moduleShiftInElement A D s (ForgetEnrichment.to (Complex A) N)) (zero_add (-s)) := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomForward_π, moduleHomForward_π, moduleShiftInElement_π,
    moduleShiftInElement_π, endomorphismClosedElement_π]
  erw [endomorphismClosedElement_π]
  simp only [mul_zero, zero_mul, Int.negOnePow_zero, one_smul,
    Cochain.units_smul_comp, Cochain.comp_units_smul]
  congr 1
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]
  simp only [Cochain.ofHom_v]
  rw [Cochain.rightShift_v _ s (-s) (neg_add_cancel s) i j hij i (add_zero i),
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) i j hij i (add_zero i)]
  simp only [Cochain.ofHom_v, id_f]
  change (𝟙 _ ≫ _) ≫ ((moduleEvaluation A D x).map (moduleShiftMap A D s f)).f j = _
  rw [moduleShiftMap_eval]
  simp only [Category.id_comp, shiftFunctorObjXIso,
    shiftFunctor_map_f']
  exact (XIsoOfEq_inv_naturality ((moduleEvaluation A D x).map f) (by omega : j + s = i)).symm

/-- 閉零射による Hom の前合成を全次数の豊穣合成として読む。 -/
lemma criterionPerfHomPrecompose_apply {M N T : ModuleCategory A D} (f : M ⟶ N)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    (eHomWhiskerRight (Complex A) f T).f q z =
      forward A (x := ForgetEnrichment.to (Complex A) M)
        (y := ForgetEnrichment.to (Complex A) N) (z := ForgetEnrichment.to (Complex A) T)
        (endomorphismClosedElement A D f) z (zero_add q) := by
  apply moduleHomElement_ext A D
  intro x
  erw [moduleHomWhiskerRight_apply_π, moduleHomForward_π, endomorphismClosedElement_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  rfl

/-- 前合成と源 shift の全 Hom chain 同型の可換図式。 -/
lemma criterionPerfHomSourceShiftIso_precompose {M N : ModuleCategory A D}
    (f : M ⟶ N) (T : RightModule A D) (s : ℤ) :
    eHomWhiskerRight (Complex A) ((moduleShiftFunctor A D s).map f)
        (ForgetEnrichment.of (Complex A) T) ≫
      (moduleHomSourceShiftIso A D (ForgetEnrichment.to (Complex A) M) T s).hom =
    (moduleHomSourceShiftIso A D (ForgetEnrichment.to (Complex A) N) T s).hom ≫
      (CategoryTheory.shiftFunctor (Complex A) (-s)).map
        (eHomWhiskerRight (Complex A) f (ForgetEnrichment.of (Complex A) T)) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (moduleHomSourceShiftIso A D (ForgetEnrichment.to (Complex A) M) T s).hom.f q
      ((eHomWhiskerRight (Complex A) ((moduleShiftFunctor A D s).map f)
        (ForgetEnrichment.of (Complex A) T)).f q z) =
    (eHomWhiskerRight (Complex A) f (ForgetEnrichment.of (Complex A) T)).f (q + -s)
      ((moduleHomSourceShiftIso A D (ForgetEnrichment.to (Complex A) N) T s).hom.f q z)
  rw [criterionPerfHomSourceShiftIso_apply, criterionPerfHomSourceShiftIso_apply,
    criterionPerfHomPrecompose_apply]
  erw [criterionPerfHomPrecompose_apply]
  rw [← forward_assoc_of_sum A _ _ _ (add_zero (-s)) (zero_add q) (by omega)]
  rw [criterionPerfModuleShiftIn_naturality]
  exact forward_assoc_of_sum A _ _ _ (zero_add (-s)) (by omega) (by omega)

end SerrePositivity.DifferentialGraded.Morita
