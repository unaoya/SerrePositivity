module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram

/-!
概要：任意の単体集合の cospan の path 引き戻しの元の三座標。
方針：二段の引き戻しの射影を合成し、両端条件を読む。
規約：充填性は不要、元の二射と全 path を保持。
使われ方：fiber ごとの path 引き戻しの値を元の値の引き戻しと比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {E D H : SSet.{u}} (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：path 引き戻しの全 path 座標。
方針：二段の第一射影。規約：元の H の path。使われ方：fiber 比較の path。 -/
def intervalPullbackPath : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback f g ⟶ (ihom (Δ[1] : SSet.{u})).obj H :=
  pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) g ≫
    pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app H) f

/-- 概要：path 引き戻しの第一入力。
方針：第一段の第二射影。規約：元の E。使われ方：fiber 比較の第一脚。 -/
def intervalPullbackLeft : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback f g ⟶ E :=
  pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) g ≫
    pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app H) f

/-- 概要：path 引き戻しの第二入力。
方針：第二段の第二射影。規約：元の D。使われ方：fiber 比較の第二脚。 -/
def intervalPullbackRight : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback f g ⟶ D :=
  pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) g

/-- 概要：指定 path の始点は元の第一射の像。
方針：第一段の可換式。規約：元の f。使われ方：fiber 比較の始点条件。 -/
lemma intervalPullbackPath_zero :
    intervalPullbackPath f g ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app H =
      intervalPullbackLeft f g ≫ f := by
  rw [intervalPullbackPath, Category.assoc, pullback.condition]
  rfl

/-- 概要：指定 path の終点は元の第二射の像。
方針：第二段の可換式。規約：元の g。使われ方：fiber 比較の終点条件。 -/
lemma intervalPullbackPath_one :
    intervalPullbackPath f g ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app H =
      intervalPullbackRight f g ≫ g := by
  change (pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) g ≫
    pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app H) f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app H = _
  rw [Category.assoc]
  exact pullback.condition

/-- 概要：path 引き戻しへの射は元の三座標で決まる。
方針：二段の引き戻しの一意性。規約：全 path を保持。使われ方：fiber 同型の往復。 -/
lemma intervalPullback_hom_ext {T : SSet.{u}} {a b : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback f g}
    (hp : a ≫ intervalPullbackPath f g = b ≫ intervalPullbackPath f g)
    (hl : a ≫ intervalPullbackLeft f g = b ≫ intervalPullbackLeft f g)
    (hr : a ≫ intervalPullbackRight f g = b ≫ intervalPullbackRight f g) : a = b := by
  apply pullback.hom_ext (f := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) (g := g)
  · apply pullback.hom_ext (f := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app H) (g := f)
    · simpa only [intervalPullbackPath, Category.assoc] using hp
    · simpa only [intervalPullbackLeft, Category.assoc] using hl
  · exact hr

end SerrePositivity.InfinityCategories.Project.FilteredExchange
