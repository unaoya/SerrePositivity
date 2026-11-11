module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackKanUnit
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackValueCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates

/-!
概要：元の三値の path 引き戻しから全空間の Kan 引き戻しへの実際の比較を照合する。
方針：値から全空間への包含と単位と元の Kan 比較を合成し、三射影を計算する。
規約：元の単位・全 path・二入力を保持する。
使われ方：標的の有限射を元の一値で検出する定理の実際の比較射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)

/-- 概要：元の値から全空間の Kan 引き戻しへ向かう構成済み比較の合成。
方針：値の包含・単位・元の比較を合成する。
規約：比較を新たに選ばない。使われ方：有限同時検出の終点。 -/
def fiberwisePullbackValueKanComparison :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g

/-- 概要：値からの比較は元の第一入力の包含と単位に一致する。
方針：単位上の比較式と値の包含式を合成する。
規約：元の第一値。使われ方：有限持ち上げの第一座標。 -/
lemma fiberwisePullbackValueKanComparison_left :
    fiberwisePullbackValueKanComparison p f g b ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (f ≫ p) b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E := by
  have h := congrArg (fun r ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g b ≫ r)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison_unit_left p f g)
  have h' := congrArg (fun r ↦ r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal_left p f g b)
  simpa only [fiberwisePullbackValueKanComparison, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft, Category.assoc]
    using h.trans h'

/-- 概要：値からの比較は元の第二入力の包含と単位に一致する。
方針：単位上の比較式と値の包含式を合成する。
規約：元の第二値。使われ方：有限持ち上げの第二座標。 -/
lemma fiberwisePullbackValueKanComparison_right :
    fiberwisePullbackValueKanComparison p f g b ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (g ≫ p) b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D := by
  have h := congrArg (fun r ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g b ≫ r)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison_unit_right p f g)
  have h' := congrArg (fun r ↦ r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal_right p f g b)
  simpa only [fiberwisePullbackValueKanComparison, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight, Category.assoc]
    using h.trans h'

/-- 概要：値からの比較は元の値の全 path を元の包含と単位で写す。
方針：単位上の全 path の式と値の包含式を合成する。
規約：両端だけでなく全円柱。使われ方：元の指定 path の有限持ち上げ。 -/
lemma fiberwisePullbackValueKanComparison_path :
    fiberwisePullbackValueKanComparison p f g b ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (f ≫ p) p f rfl b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (g ≫ p) p g rfl b) ≫
          (ihom (Δ[1] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H) := by
  have h := congrArg (fun r ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal p f g b ≫ r)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison_unit_path p f g)
  have h' := congrArg
    (fun r ↦ r ≫ (ihom (Δ[1] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H))
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackValueToTotal_path p f g b)
  simpa only [fiberwisePullbackValueKanComparison, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath, Category.assoc,
    Functor.map_comp] using h.trans h'

end SerrePositivity.InfinityCategories.Project.FilteredExchange
