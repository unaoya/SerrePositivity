module
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveZero
public import SerrePositivity.InfinityCategories.DGNerve.Algebra

/-! # 閉零対象に接する全次数の Hom の消滅

概要：閉零圏で零対象となる dg 対象に入る・出る全斉次射は零。
方針：単位の消滅を全次数の単位合成則に代入する。
規約：閉元だけでなく全成分を扱う。使われ方：β3 の零加群側の境界残差。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 閉零対象を始点とする全次数の成分は零。 -/
lemma dgGradedHom_eq_zero_of_closed_isZero_source {x y : D} {n : ℤ}
    (hx : IsZero (ForgetEnrichment.of (Complex A) x)) (f : GradedHom A x y n) : f = 0 := by
  rw [← compose_unit A f, dgUnitElement_eq_zero_of_closed_isZero x hx, compose_zero]

/-- 閉零対象を終点とする全次数の成分は零。 -/
lemma dgGradedHom_eq_zero_of_closed_isZero_target {x y : D} {n : ℤ}
    (hy : IsZero (ForgetEnrichment.of (Complex A) y)) (f : GradedHom A x y n) : f = 0 := by
  rw [← unit_compose A f, dgUnitElement_eq_zero_of_closed_isZero y hy, zero_compose]

end SerrePositivity.InfinityCategories
