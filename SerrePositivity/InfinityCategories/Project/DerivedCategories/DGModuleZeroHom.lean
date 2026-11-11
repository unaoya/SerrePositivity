module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleNerveZero
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra

/-! # 閉零対象に接する全次数の Hom の消滅

概要：閉零圏で零対象となる dg 対象に入る・出る全斉次射は零。
方針：単位の消滅を全次数の単位合成則に代入する。
規約：閉元だけでなく全成分を扱う。使われ方：β3 の零加群側の境界残差。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 閉零対象を始点とする全次数の成分は零。 -/
lemma dgGradedHom_eq_zero_of_closed_isZero_source {x y : D} {n : ℤ}
    (hx : IsZero (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y n) : f = 0 := by
  rw [← compose_unit A f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUnitElement_eq_zero_of_closed_isZero x hx, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero]

/-- 閉零対象を終点とする全次数の成分は零。 -/
lemma dgGradedHom_eq_zero_of_closed_isZero_target {x y : D} {n : ℤ}
    (hy : IsZero (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y n) : f = 0 := by
  rw [← unit_compose A f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUnitElement_eq_zero_of_closed_isZero y hy, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
