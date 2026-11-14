module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback

/-!
概要：fiber ごとの path 引き戻しの底射と、元の二入力の底射の一致。
方針：二段の引き戻しの可換式と path の両端の底の一致を使う。
規約：底も二つの入力も変更しない。
使われ方：一般 coherent な cospan の値を同じ底上の全空間として扱う。
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

/-- 概要：fiber ごとの path 引き戻しの共有する底射。
方針：path 座標の底の頂点を取る。
規約：元の底 B。使われ方：新しい図式の全空間としての射影。 -/
def fiberwiseIntervalPullbackProjection : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g ⟶ B :=
  pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalReplacementEndpoint p f) g ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) f ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p Δ[1]

/-- 概要：第一段の元の第一入力の底射は path の底射に一致。
方針：始点の引き戻し条件と始点の底射を計算する。
規約：厳密に一致。使われ方：元の第一入力の底を保つ。 -/
lemma fiberwiseIntervalReplacement_left_projection :
    pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) f ≫ f ≫ p =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) f ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p Δ[1] := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint_projection]

/-- 概要：元の第一入力から読んだ底射は共有する底射。
方針：第一段の底射の等式を第二段の第一射影で前合成する。
規約：元の指定第一射 f。使われ方：底上の cospan の整合。 -/
lemma fiberwiseIntervalPullback_left_projection :
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalReplacementEndpoint p f) g ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) f ≫ f ≫ p =
        fiberwiseIntervalPullbackProjection p f g := by
  rw [fiberwiseIntervalReplacement_left_projection]
  rfl

/-- 概要：元の第二入力から読んだ底射も共有する底射。
方針：第二段の引き戻し条件と終点の底射を計算する。
規約：元の指定第二射 g。使われ方：同じ底上の二入力の厳密な一致。 -/
lemma fiberwiseIntervalPullback_right_projection :
    pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalReplacementEndpoint p f) g ≫ g ≫ p =
      fiberwiseIntervalPullbackProjection p f g := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc]
  change pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalReplacementEndpoint p f) g ≫
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0) f ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 1) ≫ p = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint_projection]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
