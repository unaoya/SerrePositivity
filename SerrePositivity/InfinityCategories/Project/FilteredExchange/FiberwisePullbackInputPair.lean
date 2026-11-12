module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullbackMaps

/-!
概要：fiber ごとの path 引き戻しの二入力を、同じ底の二対象の組へ送る。
方針：元の両入力の底射の一致を使う。
規約：入力の底射は f ≫ p と g ≫ p。
使われ方：相対両端評価の引き戻しとしての一段の表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：元の二入力を共有する底上の積へまとめる。
方針：元の二つの底射が同じ共有底射に一致することを使う。
規約：元の E と D。使われ方：底上の cospan の両端の指定。 -/
def fiberwisePullbackInputPair : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g ⟶
    pullback (f ≫ p) (g ≫ p) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g)
    ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback_left_projection p f g).trans
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback_right_projection p f g).symm)

/-- 概要：二入力の組の第一射影は元の第一入力。
方針：引き戻しの第一射影。規約：厳密な一致。使われ方：両端の持ち上げ。 -/
lemma fiberwisePullbackInputPair_fst :
    fiberwisePullbackInputPair p f g ≫ pullback.fst (f ≫ p) (g ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g := pullback.lift_fst _ _ _

/-- 概要：二入力の組の第二射影は元の第二入力。
方針：引き戻しの第二射影。規約：厳密な一致。使われ方：両端の持ち上げ。 -/
lemma fiberwisePullbackInputPair_snd :
    fiberwisePullbackInputPair p f g ≫ pullback.snd (f ≫ p) (g ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g := pullback.lift_snd _ _ _

/-- 概要：二入力を元の二射で同じ底の二対象へ送る。
方針：元の f・g と底の恒等射を引き戻しへ写す。
規約：元の H の fiber ごとの積。使われ方：相対両端評価の引き戻しの下辺。 -/
def fiberwiseCospanPair : pullback (f ≫ p) (g ≫ p) ⟶ pullback p p :=
  pullback.map (f ≫ p) (g ≫ p) p p f g (𝟙 B)
    (by rw [Category.comp_id]) (by rw [Category.comp_id])

/-- 概要：二入力の像の組の第一射影は元の第一射による像。
方針：引き戻しの第一射影。規約：元の f。使われ方：両端の指定式。 -/
lemma fiberwiseCospanPair_fst :
    fiberwiseCospanPair p f g ≫ pullback.fst p p = pullback.fst (f ≫ p) (g ≫ p) ≫ f :=
  pullback.lift_fst _ _ _

/-- 概要：二入力の像の組の第二射影は元の第二射による像。
方針：引き戻しの第二射影。規約：元の g。使われ方：両端の指定式。 -/
lemma fiberwiseCospanPair_snd :
    fiberwiseCospanPair p f g ≫ pullback.snd p p = pullback.snd (f ≫ p) (g ≫ p) ≫ g :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
