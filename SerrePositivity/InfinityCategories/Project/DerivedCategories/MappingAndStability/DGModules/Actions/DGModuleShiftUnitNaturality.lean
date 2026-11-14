module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleClosedRightShift
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift

/-! # 未正規化の斉次 shift 単位の閉射に関する自然性

概要：shift の斉次射影・包含は閉加群射と可換である。
方針：正規化済み射影の自然性から定数符号を消し、両逆関係で包含へ移す。
規約：整数 shift の定数符号を保持する。使われ方：全次数の右 shift と商比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 未正規化の斉次射影も閉加群射に関して自然。 -/
lemma dgModuleShiftOut_naturality (n : ℤ) {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N) :
    _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D n (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N))
      (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (M⟦n⟧) (N⟦n⟧) (f⟦n⟧')).val (zero_add n) =
    _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) M N f).val
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D n (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)) (add_zero n) := by
  have h := _root_.SerrePositivity.DifferentialGraded.normalizedModuleShiftOut_naturality A D n f
  simp only [_root_.SerrePositivity.DifferentialGraded.forward_eq_signed_compose, Int.zero_mul, Int.mul_zero,
    Int.negOnePow_zero, one_smul] at h
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left (A := A) (D := RightModule A D)
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftNormalizationExponent n).negOnePow
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D n (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N))
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (M⟦n⟧) (N⟦n⟧) (f⟦n⟧')).val (zero_add n)
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right (A := A) (D := RightModule A D)
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftNormalizationExponent n).negOnePow
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) M N f).val
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D n (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)) (add_zero n)
  exact smul_left_cancel (_root_.SerrePositivity.DifferentialGraded.moduleShiftNormalizationExponent n).negOnePow
    (hl.symm.trans (h.trans hr))

/-- 斉次射影による後合成は、次数 −n の Hom 元の等号を反映する。 -/
lemma dgModuleShiftOut_cancel (n : ℤ) {L N : _root_.SerrePositivity.DifferentialGraded.RightModule A D}
    (a b : _root_.SerrePositivity.DifferentialGraded.GradedHom A L (_root_.SerrePositivity.DifferentialGraded.shiftModule n N) (-n))
    (h : _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D n N) a (neg_add_cancel n) =
      _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D n N) b (neg_add_cancel n)) : a = b := by
  have hr (z : _root_.SerrePositivity.DifferentialGraded.GradedHom A L (_root_.SerrePositivity.DifferentialGraded.shiftModule n N) (-n)) :
      _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement A D n N)
        (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D n N) z (neg_add_cancel n)) (zero_add (-n)) = z := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum z (moduleShiftOutElement A D n N) (moduleShiftInElement A D n N)
      (neg_add_cancel n) (add_neg_cancel n) (zero_add (-n)), _root_.SerrePositivity.DifferentialGraded.moduleShiftOutIn, _root_.SerrePositivity.DifferentialGraded.unit_compose]
  exact (hr a).symm.trans ((congrArg (fun z : _root_.SerrePositivity.DifferentialGraded.GradedHom A L N 0 =>
    _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement A D n N) z (zero_add (-n))) h).trans (hr b))

/-- 斉次包含は閉加群射とその shift に関して自然。 -/
lemma dgModuleShiftIn_naturality (n : ℤ) {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N) :
    _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (M⟦n⟧) (N⟦n⟧) (f⟦n⟧')).val
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement A D n (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)) (add_zero (-n)) =
    _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement A D n (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N))
      (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) M N f).val (zero_add (-n)) := by
  let m := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M
  let t := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N
  let a : GradedHom A m t 0 := (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) M N f).val
  let b : _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.shiftModule n m) (_root_.SerrePositivity.DifferentialGraded.shiftModule n t) 0 :=
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (M⟦n⟧) (N⟦n⟧) (f⟦n⟧')).val
  change _root_.SerrePositivity.DifferentialGraded.compose A b (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement A D n m) (add_zero (-n)) =
    _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement A D n t) a (zero_add (-n))
  have hn : _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D n t) b (zero_add n) =
      _root_.SerrePositivity.DifferentialGraded.compose A a (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D n m) (add_zero n) :=
    dgModuleShiftOut_naturality A D n f
  apply dgModuleShiftOut_cancel A D n
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (add_zero (-n)) (zero_add n) (neg_add_cancel n), hn,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (neg_add_cancel n) (add_zero n) (add_zero 0),
    _root_.SerrePositivity.DifferentialGraded.moduleShiftInOut A D n m, _root_.SerrePositivity.DifferentialGraded.compose_unit,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (zero_add (-n)) (neg_add_cancel n) (neg_add_cancel n),
    _root_.SerrePositivity.DifferentialGraded.moduleShiftInOut A D n t, _root_.SerrePositivity.DifferentialGraded.unit_compose]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
