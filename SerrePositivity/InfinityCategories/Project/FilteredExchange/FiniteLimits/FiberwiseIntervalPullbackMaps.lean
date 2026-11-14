module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback

/-!
概要：fiber ごとの二段の path 引き戻しの元の三座標と両端の指定式。
方針：二段の引き戻しの第一・第二射影を合成する。
規約：path は底を固定した元の path 全体。
使われ方：全空間 Kan 模型間の実際の引き戻し比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：元の path 引き戻しの底を固定した全 path 座標。
方針：二段の第一射影を合成。規約：元の p。使われ方：指定 path の Kan 比較。 -/
def fiberwiseIntervalPullbackPath : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g ⟶
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p (Δ[1] : SSet.{u}) :=
  pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalReplacementEndpoint p f) g ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) f

/-- 概要：元の path 引き戻しの第一入力。
方針：第一射影の後に第一段の第二射影。規約：元の E。使われ方：第一脚の Kan 比較。 -/
def fiberwiseIntervalPullbackLeft : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g ⟶ E :=
  pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalReplacementEndpoint p f) g ≫
    pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) f

/-- 概要：元の path 引き戻しの第二入力。
方針：第二段の第二射影。規約：元の D。使われ方：第二脚の Kan 比較。 -/
def fiberwiseIntervalPullbackRight : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g ⟶ D :=
  pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalReplacementEndpoint p f) g

/-- 概要：元の全 path の始点は元の第一入力の像。
方針：第一段の引き戻し条件を合成する。
規約：元の f。使われ方：Kan path 比較の始点の指定等式。 -/
lemma fiberwiseIntervalPullbackPath_zero :
    fiberwiseIntervalPullbackPath p f g ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0 =
      fiberwiseIntervalPullbackLeft p f g ≫ f := by
  rw [fiberwiseIntervalPullbackPath, Category.assoc, pullback.condition]
  rfl

/-- 概要：元の全 path の終点は元の第二入力の像。
方針：第二段の引き戻し条件を使う。
規約：元の g。使われ方：Kan path 比較の終点の指定等式。 -/
lemma fiberwiseIntervalPullbackPath_one :
    fiberwiseIntervalPullbackPath p f g ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 1 =
      fiberwiseIntervalPullbackRight p f g ≫ g := by
  change (pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalReplacementEndpoint p f) g ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) f) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 1 = _
  rw [Category.assoc]
  exact pullback.condition

/-- 概要：fiber ごとの path 引き戻しへの射は元の三座標で決まる。
方針：二段の引き戻しの射影による一意性を使う。
規約：path は底を固定した全 path。使われ方：一段の相対両端引き戻しとの比較。 -/
lemma fiberwiseIntervalPullback_hom_ext {T : SSet.{u}}
    {a b : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g}
    (hp : a ≫ fiberwiseIntervalPullbackPath p f g = b ≫ fiberwiseIntervalPullbackPath p f g)
    (hl : a ≫ fiberwiseIntervalPullbackLeft p f g = b ≫ fiberwiseIntervalPullbackLeft p f g)
    (hr : a ≫ fiberwiseIntervalPullbackRight p f g = b ≫ fiberwiseIntervalPullbackRight p f g) :
    a = b := by
  apply pullback.hom_ext (f := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalReplacementEndpoint p f) (g := g)
  · apply pullback.hom_ext (f := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) (g := f)
    · simpa only [fiberwiseIntervalPullbackPath, Category.assoc] using hp
    · simpa only [fiberwiseIntervalPullbackLeft, Category.assoc] using hl
  · exact hr

end SerrePositivity.InfinityCategories.Project.FilteredExchange
