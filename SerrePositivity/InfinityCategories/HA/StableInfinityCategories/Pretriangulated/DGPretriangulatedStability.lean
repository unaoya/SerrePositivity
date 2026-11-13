module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRepleteYonedaStability
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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated
open _root_.CategoryTheory _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 前三角 dg 圏の実 dg nerve は元の宇宙で安定である。 -/
theorem dgNerve_isStable_of_pretriangulated [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_ulift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveULift_isStable_of_pretriangulated A D)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.0.2" (partial := component) "仮定：前三角 dg 圏（Lean が弱い：体に限らず可換環上でよい）。結論：その dg nerve が安定。体上の加群スペクトルで豊穣化した安定 ∞ 圏から dg 圏を復元する逆向きと豊穣化の比較は得られない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated
