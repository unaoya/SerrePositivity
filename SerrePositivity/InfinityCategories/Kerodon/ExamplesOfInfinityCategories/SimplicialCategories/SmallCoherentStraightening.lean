module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallWitnessContractible

/-!
概要：次数ごとに小さい全空間の left fibration に実際の coherent な分類図式を与える。
方針：非空な可縮表現空間から表現を選び、既証明の全空間比較を回収する。
規約：ここでは対象ごとの構成であり、関手性や単位・余単位を主張しない。
使われ方：一般の単体集合を底とする straightening の対象側の主経路。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：任意の底上の小さい全空間の left fibration の実際の表現を選ぶ。
方針：可縮な表現空間から得た非空性を使う。
規約：選択の一意性は表現空間の可縮性による。
使われ方：coherent な分類図式と比較射の構成。 -/
def smallLeftStraighteningRepresentation {E B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p := Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftTransportRepresentation_nonempty p)

/-- 概要：小さい全空間の left fibration の coherent な空間値分類図式。
方針：選んだ実際の表現の分類図式を取る。
規約：底を通常の圏の nerve に制限しない。
使われ方：straightening の対象上の値。 -/
def smallLeftStraighteningDiagram {E B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (smallLeftStraighteningRepresentation p).diagram

/-- 概要：元の全空間から分類図式の unstraightening への実際の比較射。
方針：選んだ表現の比較射を取る。
規約：底上の射として構成する。
使われ方：元の left fibration の復元。 -/
def smallLeftStraighteningComparison {E B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (smallLeftStraighteningDiagram p) :=
  (smallLeftStraighteningRepresentation p).comparison

/-- 概要：分類図式への比較は底への射影と厳密に可換。
方針：表現の底上の条件を回収する。
規約：ホモトピー可換に弱めない。
使われ方：元の left fibration と復元の底上の比較。 -/
lemma smallLeftStraighteningComparison_over_base {E B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    smallLeftStraighteningComparison p ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (smallLeftStraighteningDiagram p) = p :=
  (smallLeftStraighteningRepresentation p).over_base

/-- 概要：分類図式への比較は全空間の前合成同値。
方針：表現の各 fiber の同値性を全空間の比較へ渡す。
規約：底の quasicategory 性は不要。
使われ方：任意の底上の分類図式から元の全空間を同値まで復元する。 -/
lemma smallLeftStraighteningComparison_isPrecompositionEquivalence {E B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (smallLeftStraighteningComparison p) :=
  (smallLeftStraighteningRepresentation p).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
