module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ZeroShift

/-!
概要：零 shift の斉次包含は同じ零 shift 同型の逆閉零射。
方針：全評価 cochain の成分を照合する。
規約：元の shift の符号を保持する。
使われ方：零次元層の閉包含を標準頂点射へ比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarShiftIn_zero (M : RightModule R D) :
    moduleShiftInElement R D 0 M =
      (closedHomEquiv R (RightModule R D)
        (ForgetEnrichment.of (Complex R) M)
        (ForgetEnrichment.of (Complex R) (shiftModule 0 M)) (moduleShiftZeroIsoObj R D M).inv).val := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleShiftInElement_π]
  refine Eq.trans ?_ (moduleEvaluation_cochain R D x (moduleShiftZeroIsoObj R D M).inv)
  rw [moduleShiftZeroIsoObj_inv_eval]
  simp only [zero_mul, mul_zero, zero_add, Int.zero_ediv, Int.negOnePow_zero, one_smul]
  apply Cochain.ext₀
  intro i
  rw [Cochain.rightShift_v _ 0 (-0) (neg_add_cancel 0) i i (add_zero i) i (add_zero i)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f,
    CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorObjXIso,
    Category.comp_id, Category.id_comp, add_zero, zero_add, Int.neg_zero,
    HomologicalComplex.XIsoOfEq, sub_zero, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
