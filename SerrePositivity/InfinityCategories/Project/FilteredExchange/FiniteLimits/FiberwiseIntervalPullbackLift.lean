module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps

/-!
概要：元の二入力と指定された底固定 path からの fiber ごとの引き戻しへの持ち上げ。
方針：両端の指定等式で二段の引き戻しへ入れる。
規約：元の三座標を厳密に保持する。
使われ方：相対両端評価による引き戻しの一段の表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {T E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)
  (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p (Δ[1] : SSet.{u})) (b : T ⟶ E) (c : T ⟶ D)
  (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0 = b ≫ f)
  (hb : a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 1 = c ≫ g)

/-- 概要：指定された二入力と底固定の全 path の引き戻しへの持ち上げ。
方針：始点条件と終点条件を順に使う。
規約：元の両端等式。使われ方：一段の相対持ち上げの普遍性。 -/
def fiberwiseIntervalPullbackLift : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g :=
  pullback.lift (pullback.lift a b ha) c (by
    change pullback.lift a b ha ≫
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) f ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 1) = _
    rw [← Category.assoc, pullback.lift_fst]
    exact hb)

/-- 概要：持ち上げの path は元の指定 path 全体。
方針：二段の第一射影。規約：全単体で一致。使われ方：相対持ち上げの検査。 -/
lemma fiberwiseIntervalPullbackLift_path :
    fiberwiseIntervalPullbackLift p f g a b c ha hb ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath p f g = a := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath, ← Category.assoc, fiberwiseIntervalPullbackLift,
    pullback.lift_fst, pullback.lift_fst]

/-- 概要：持ち上げの第一入力は元の指定第一入力。
方針：第一段の第二射影。規約：厳密な等式。使われ方：入力の照合。 -/
lemma fiberwiseIntervalPullbackLift_left :
    fiberwiseIntervalPullbackLift p f g a b c ha hb ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g = b := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft, ← Category.assoc, fiberwiseIntervalPullbackLift,
    pullback.lift_fst, pullback.lift_snd]

/-- 概要：持ち上げの第二入力は元の指定第二入力。
方針：第二段の第二射影。規約：厳密な等式。使われ方：入力の照合。 -/
lemma fiberwiseIntervalPullbackLift_right :
    fiberwiseIntervalPullbackLift p f g a b c ha hb ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g = c :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
