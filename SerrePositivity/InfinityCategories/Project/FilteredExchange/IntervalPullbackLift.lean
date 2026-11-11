module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates

/-!
概要：元の三座標から path 引き戻しへの厳密な持ち上げ。
方針：指定された始点・終点の式で二段の引き戻しへ入れる。
規約：元の全 path を選び直さない。
使われ方：fiber の path 引き戻しとの同型の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {T E D H : SSet.{u}} (f : E ⟶ H) (g : D ⟶ H)
  (a : T ⟶ (ihom (Δ[1] : SSet.{u})).obj H) (b : T ⟶ E) (c : T ⟶ D)
  (ha : a ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app H = b ≫ f)
  (hb : a ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app H = c ≫ g)

/-- 概要：元の三座標を path 引き戻しへ持ち上げる。
方針：始点条件と終点条件を順に使う。
規約：充填性は不要。使われ方：fiber 比較の構成。 -/
def intervalPullbackLift : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback f g :=
  pullback.lift (pullback.lift a b ha) c (by
    change pullback.lift a b ha ≫
      (pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app H) f ≫
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app H) = _
    rw [← Category.assoc, pullback.lift_fst]
    exact hb)

/-- 概要：持ち上げは指定全 path を保持する。
方針：二段の第一射影。規約：厳密な一致。使われ方：fiber 比較の path 座標。 -/
lemma intervalPullbackLift_path :
    intervalPullbackLift f g a b c ha hb ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath f g = a := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath, ← Category.assoc, intervalPullbackLift,
    pullback.lift_fst, pullback.lift_fst]

/-- 概要：持ち上げは指定第一入力を保持する。
方針：第一段の第二射影。規約：厳密な一致。使われ方：fiber 比較の第一脚。 -/
lemma intervalPullbackLift_left :
    intervalPullbackLift f g a b c ha hb ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft f g = b := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft, ← Category.assoc, intervalPullbackLift,
    pullback.lift_fst, pullback.lift_snd]

/-- 概要：持ち上げは指定第二入力を保持する。
方針：第二段の第二射影。規約：厳密な一致。使われ方：fiber 比較の第二脚。 -/
lemma intervalPullbackLift_right :
    intervalPullbackLift f g a b c ha hb ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight f g = c :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
