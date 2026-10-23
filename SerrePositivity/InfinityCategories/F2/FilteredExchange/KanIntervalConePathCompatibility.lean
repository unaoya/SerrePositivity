module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanIntervalConeLeftImagePath
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanIntervalConeRightImageProjection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalPullbackPathIsoComparison

/-!
概要：元の区間引き戻し path と native 極限錐の二射影・指定可換性の最終整合。
方針：左右の像比較に元の path の同型と終点の等式を合成する。
規約：元の指定 path・脚比較・二単体の値を保持。使われ方：coherent filtered 交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Y Z : KanObject.{u}}

/-- 概要：元の二射影の指定比較と元の全 path は native 錐の指定可換性に対して整合。
方針：同じ全円柱の像比較と元の path の厳密な同定を合成。
規約：指定同型の値の等式。使われ方：元の cospan の極限と全空間比較の接続。 -/
lemma intervalPullbackCone_projection_commutativity (f : X ⟶ Y) (g : Z ⟶ Y) :
    (intervalPullbackConeFstIso f g).postcomp f ≪≫ intervalPullbackPathIso f g =
      intervalPullbackConeNativeCommutativity f g ≪≫
        (intervalPullbackConeSndIso f g).postcomp g := by
  rw [← intervalPullbackPathIso_comparison, ← Iso.trans_assoc,
    intervalPullbackConeLeftImageIso_path, ← intervalPullbackConeImageIso_commutativity,
    Iso.trans_assoc, intervalPullbackConeRightImageIso_projection]

end SerrePositivity.InfinityCategories.F2
