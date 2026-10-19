module
public import SerrePositivity.InfinityCategories.Derived.DGModuleBicartesianChoices
public import SerrePositivity.InfinityCategories.Stable.BicartesianCriterion

/-! # 全 Hom end を持つ dg 加群 nerve の安定性

概要：dg 加群 nerve は実零対象と全辺の双カルテジアンな fiber/cofiber を持ち、安定。
方針：標準 cone/shifted cone の普遍性を任意の零角四角形へ関手同型で輸送する。
規約：h の三角構造から安定性を逆算しない。使われ方：β3 の前三角 dg 圏と商の模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 任意の零角 dg 加群四角形について fiber 列と cofiber 列は同値。 -/
lemma dgModuleNerve_fiber_iff_cofiber (t : ZeroTriangle (dgModuleNerve A D)) :
    IsFiberSequence t ↔ IsCofiberSequence t :=
  zeroTriangle_fiber_iff_cofiber_of_bicartesian_choices
    (dgModuleNerve_bicartesian_fiber_exists A D)
    (dgModuleNerve_bicartesian_cofiber_exists A D) t

/-- 全 Hom end を持つ任意の小さい dg 圏上の dg 加群の nerve は安定。 -/
instance dgModuleNerve_isStable : IsStable (dgModuleNerve A D) :=
  isStable_of_bicartesian_choices (dgModuleNerve_bicartesian_fiber_exists A D)
    (dgModuleNerve_bicartesian_cofiber_exists A D)

end SerrePositivity.InfinityCategories
