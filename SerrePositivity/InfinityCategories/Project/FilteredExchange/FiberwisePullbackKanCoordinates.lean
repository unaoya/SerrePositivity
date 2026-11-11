module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram

/-!
概要：全空間 Kan cospan への引き戻し比較の三座標の厳密な式。
方針：二段の引き戻しの射影と選択した path 比較の単位式を計算する。
規約：元の二入力と単位上の全 path を保持する。
使われ方：一般 coherent filtered 引き戻し交換の指定比較の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：第一段の第一射影は元の path 座標の Kan 比較。
方針：引き戻しの第一射影。規約：全 path。使われ方：比較の path 座標。 -/
lemma fiberwisePullbackKanReplacementComparison_path :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanReplacementComparison p f g ≫
      pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj H))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath p f g) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparison p := pullback.lift_fst _ _ _

/-- 概要：第一段の第二射影は元の第一入力の Kan 射影。
方針：引き戻しの第二射影。規約：元の第一入力。使われ方：比較の第一脚。 -/
lemma fiberwisePullbackKanReplacementComparison_left :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanReplacementComparison p f g ≫
      pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj H))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g) :=
  pullback.lift_snd _ _ _

/-- 概要：第二段の第一射影は元の第一段の比較。
方針：引き戻しの第一射影。規約：選んだ比較そのもの。使われ方：全座標の式。 -/
lemma fiberwisePullbackKanComparison_fst :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanReplacementComparison p f g :=
  pullback.lift_fst _ _ _

/-- 概要：第二段の第二射影は元の第二入力の Kan 射影。
方針：引き戻しの第二射影。規約：元の第二入力。使われ方：比較の第二脚。 -/
lemma fiberwisePullbackKanComparison_right :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g) :=
  pullback.lift_snd _ _ _

/-- 概要：全比較の第一脚は元の第一入力の Kan 射影。
方針：二段の射影式を合成。規約：元の E。使われ方：cospan の比較の第一脚。 -/
lemma fiberwisePullbackKanComparison_left :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) ≫
      pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj H))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g) := by
  rw [← Category.assoc, fiberwisePullbackKanComparison_fst,
    fiberwisePullbackKanReplacementComparison_left]

/-- 概要：全比較の path は元の全 path 座標の選んだ Kan 比較。
方針：二段の第一射影を合成。規約：全単体で一致。使われ方：指定 path の照合。 -/
lemma fiberwisePullbackKanComparison_path :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) ≫
      pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj H))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath p f g) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparison p := by
  rw [← Category.assoc, fiberwisePullbackKanComparison_fst,
    fiberwisePullbackKanReplacementComparison_path]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
