module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingZeroVertex

/-! # 閉零圏の零対象から dg nerve の実零頂点へ

概要：閉零圏の零対象は零の収縮元を持ち、nerve の実零対象になる。
方針：恒等射と零射の一致を単位の次数零成分で評価する。
規約：h の零対象性とは区別する。使われ方：β3 の dg 加群圏の零対象。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 閉零圏の零対象では、dg 単位の実際の次数零成分は零。 -/
lemma dgUnitElement_eq_zero_of_closed_isZero (x : D)
    (hx : IsZero (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) : (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val = 0 := by
  have h := hx.eq_of_src (𝟙 (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) 0
  have hh := congrArg (fun f => (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit (_root_.SerrePositivity.DifferentialGraded.homObject A D x x)
    (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val) h
  change (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val = (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit (_root_.SerrePositivity.DifferentialGraded.homObject A D x x) 0).val at hh
  change (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val = 0 at hh
  exact hh

/-- 閉零圏の零対象は実際の dg nerve の始対象かつ終対象。 -/
lemma dgNerve_isZeroVertex_of_closed_isZero (x : D)
    (hx : IsZero (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isZeroVertex x (0 : GradedHom A x x (-1))
  rw [map_zero, dgUnitElement_eq_zero_of_closed_isZero x hx]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
