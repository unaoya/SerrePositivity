module
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-!
概要：零 shift の斉次射影を、既存の零 shift 同型の閉零射として読む。
方針：評価した cochain の全成分を照合する。
規約：shift の符号と全 dg 自然性を保持する。
使われ方：strict augmentation の一次元係数の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgStrictShiftOut_zero (M : RightModule R D) :
    moduleShiftOutElement R D 0 M =
      (closedHomEquiv R (RightModule R D)
        (ForgetEnrichment.of (Complex R) (shiftModule 0 M))
        (ForgetEnrichment.of (Complex R) M) (moduleShiftZeroIsoObj R D M).hom).val := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleShiftOutElement_π]
  refine Eq.trans ?_ (moduleEvaluation_cochain R D x (moduleShiftZeroIsoObj R D M).hom)
  rw [moduleShiftZeroIsoObj_hom_eval]
  change (Cochain.ofHom (𝟙 (M.obj (Opposite.op x)))).leftShift 0 0 (zero_add 0) =
    Cochain.ofHom ((shiftFunctorZero (Complex R) ℤ).hom.app (M.obj (Opposite.op x)))
  apply Cochain.ext₀
  intro i
  rw [Cochain.leftShift_v _ 0 0 (zero_add 0) i i (add_zero i) i (add_zero i)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f,
    CochainComplex.shiftFunctorZero_hom_app_f, CochainComplex.shiftFunctorObjXIso,
    Category.comp_id, zero_mul, zero_add, Int.zero_ediv, Int.negOnePow_zero, one_smul]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
