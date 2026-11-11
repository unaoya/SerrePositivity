module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram

/-!
概要：選んだ Kan path 比較の、元の path 全体と二つの端点の厳密な一致。
方針：指定可換四角形の持ち上げの両三角形を読む。
規約：選択した比較射そのものを追跡する。
使われ方：二入力を保つ一般 coherent な引き戻し比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

private instance comparisonLifting {E B : SSet.{u}} (p : E ⟶ B) :
    HasLiftingProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p Δ[1]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p Δ[1]) _
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)

/-- 概要：比較の単位への制限は元の path を全空間の単位で写した射そのもの。
方針：持ち上げの左三角形を読む。
規約：全 path 座標。使われ方：元の fiber の指定 path の保持。 -/
lemma fiberwiseIntervalKanComparison_unit {E B : SSet.{u}} (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorSpace p Δ[1]) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparison p =
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram Δ[1] B) ≫
          (ihom (Δ[1] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparisonSquare p).fac_left

/-- 概要：比較の両端は元の二評価の Kan 置換の組。
方針：持ち上げの右三角形を読む。
規約：二端点を同時に固定。使われ方：比較射を指定した cospan へ制限する。 -/
lemma fiberwiseIntervalKanComparison_boundary {E B : SSet.{u}} (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparison p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E) =
      lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 1)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparisonSquare p).fac_right

/-- 概要：比較は各指定端点の元の評価の Kan 置換に厳密に重なる。
方針：両端の式を第一・第二射影で読む。
規約：0 は始点、1 は終点。使われ方：二段の引き戻しの厳密な比較。 -/
lemma fiberwiseIntervalKanComparison_endpoint {E B : SSet.{u}} (p : E ⟶ B) (e : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparison p ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans e).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p e) := by
  fin_cases e
  · change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparison p ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 0)
    have h := congrArg (fun r ↦ r ≫ fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)) (fiberwiseIntervalKanComparison_boundary p)
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans, Category.assoc, lift_fst] using h
  · change _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalKanComparison p ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpoint p 1)
    have h := congrArg (fun r ↦ r ≫ snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)) (fiberwiseIntervalKanComparison_boundary p)
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans, Category.assoc, lift_snd] using h

end SerrePositivity.InfinityCategories.Project.FilteredExchange
