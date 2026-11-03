module
public import SerrePositivity.InfinityCategories.Derived.Gluing.Pretriangulated
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedStability
public import SerrePositivity.InfinityCategories.Stable.Idempotent.StabilityUniverse
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingNerve_isStable : IsStable (dgNerve R (DGGluingObject R C D M)) := by
  let := dgGluing_isDGPretriangulated R C D M hC hD
  exact dgNerve_isStable_of_pretriangulated R (DGGluingObject R C D M)
lemma dgGluingUniverseNerve_isStable :
    IsStable ((SSet.uliftFunctor.{max (u + 1) v w,max u v w}).obj
      (dgNerve R (DGGluingObject R C D M))) := by
  let := dgGluingNerve_isStable R C D M hC hD
  exact F2.Idempotent.isStable_ulift
end SerrePositivity.InfinityCategories
