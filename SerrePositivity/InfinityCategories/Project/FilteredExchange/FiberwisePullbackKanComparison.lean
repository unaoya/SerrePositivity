module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalKanCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram

/-!
概要：fiber ごとの path 引き戻しの全空間 Kan 模型から、元の Kan cospan の path 引き戻しへの比較。
方針：path の Kan 比較の両端の厳密な一致で、元の二つの入力を順に引き戻す。
規約：比較は元の二射と選んだ path 比較を保持する。
使われ方：一般 coherent な cospan の filtered 余極限と引き戻しの交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：第一入力と元の path の Kan 比較を、Kan cospan の第一段へ入れる。
方針：path の始点の厳密な式を使って引き戻しへ持ち上げる。
規約：元の第一射 f の Kan 置換。使われ方：全比較の第一段。 -/
def fiberwisePullbackKanReplacementComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath p f g) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparison p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g)) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparison_endpoint,
        ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath_zero,
        CategoryTheory.Functor.map_comp])

/-- 概要：第一段の終点は元の第二入力の像の Kan 置換。
方針：path 比較の終点と元の引き戻しの終点条件を計算する。
規約：元の第二射 g。使われ方：第二段への厳密な持ち上げ。 -/
lemma fiberwisePullbackKanReplacementComparison_endpoint :
    fiberwisePullbackKanReplacementComparison p f g ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g := by
  change fiberwisePullbackKanReplacementComparison p f g ≫
    (pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj H))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj H)) = _
  rw [← Category.assoc, fiberwisePullbackKanReplacementComparison, pullback.lift_fst,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparison_endpoint,
    ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath_one,
    CategoryTheory.Functor.map_comp]

/-- 概要：元の fiber ごとの path 引き戻しから、Kan 模型の cospan の引き戻しへの実際の比較。
方針：第一段の終点式で第二入力の Kan 射影を引き戻す。
規約：元の三つの全空間を各 Kan 模型へ写す。使われ方：filtered 引き戻し交換の比較射。 -/
def fiberwisePullbackKanComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) :=
  pullback.lift (fiberwisePullbackKanReplacementComparison p f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g))
    (fiberwisePullbackKanReplacementComparison_endpoint p f g)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
