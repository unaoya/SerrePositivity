module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepleteYonedaStability
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseStabilityDescent

/-! # 前三角 dg 圏の dg nerve の安定性

概要：前三角 dg 圏の元の dg nerve は元の宇宙のままで安定。
方針：実 Yoneda 同値で得た ULift の安定性を、全実四角形の宇宙比較で降下する。
規約：安定性を H⁰ の三角構造だけから定義しない。使われ方：β3 の商の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 前三角 dg 圏の実 dg nerve は元の宇宙で安定である。 -/
theorem dgNerve_isStable_of_pretriangulated [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_ulift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveULift_isStable_of_pretriangulated A D)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
