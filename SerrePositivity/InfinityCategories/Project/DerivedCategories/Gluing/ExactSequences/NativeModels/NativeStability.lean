module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Pretriangulated
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.DGPretriangulatedStability
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Idempotent.StabilityUniverse
/-!
概要：元の二 dg 圏が前三角的なら、元 dg gluing の nerve と共通宇宙の nerve は安定である。
方針：既存の実前三角性から native 安定性を得て、同じ単体集合の宇宙持ち上げへ移す。
規約：元対象・Hom 複体を保持し、モデル圏構造の仮定を追加しない。
使われ方：安定 gluing の二射影と導来 lax pullback 比較の完全性を接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
include hC hD
lemma dgGluingNerve_isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
lemma dgGluingUniverseNerve_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max u v w}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))) := by
  let := dgGluingNerve_isStable R C D M hC hD
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Idempotent.isStable_ulift
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
