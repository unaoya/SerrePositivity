module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.EssentiallySmallWitnessContractible

/-!
概要：essentially small fiber を持つ left fibration に実際の coherent な分類図式を与える。
方針：非空な可縮表現空間から表現を選び、既証明の全空間比較を回収する。
規約：ここでは対象ごとの構成であり、関手性や単位・余単位を主張しない。
使われ方：一般の単体集合を底とする straightening の対象側の主経路。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：任意の底上のessentially small fiber を持つ left fibration の実際の表現を選ぶ。
方針：可縮な表現空間から得た非空性を使う。
規約：選択の一意性は表現空間の可縮性による。
使われ方：coherent な分類図式と比較射の構成。 -/
def essentiallySmallLeftStraighteningRepresentation {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.essentiallySmallLeftTransportRepresentation_nonempty p hp)

/-- 概要：essentially small fiber を持つ left fibration の coherent な空間値分類図式。
方針：選んだ実際の表現の分類図式を取る。
規約：底を通常の圏の nerve に制限しない。
使われ方：straightening の対象上の値。 -/
def essentiallySmallLeftStraighteningDiagram {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers p) : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (essentiallySmallLeftStraighteningRepresentation p hp).diagram

/-- 概要：元の全空間から分類図式の unstraightening への実際の比較射。
方針：選んだ表現の比較射を取る。
規約：底上の射として構成する。
使われ方：元の left fibration の復元。 -/
def essentiallySmallLeftStraighteningComparison {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers p) :
    E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (essentiallySmallLeftStraighteningDiagram p hp) :=
  (essentiallySmallLeftStraighteningRepresentation p hp).comparison

/-- 概要：分類図式への比較は底への射影と厳密に可換。
方針：表現の底上の条件を回収する。
規約：ホモトピー可換に弱めない。
使われ方：元の left fibration と復元の底上の比較。 -/
lemma essentiallySmallLeftStraighteningComparison_over_base {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers p) :
    essentiallySmallLeftStraighteningComparison p hp ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (essentiallySmallLeftStraighteningDiagram p hp) = p :=
  (essentiallySmallLeftStraighteningRepresentation p hp).over_base

/-- 概要：分類図式への比較は全空間の前合成同値。
方針：表現の各 fiber の同値性を全空間の比較へ渡す。
規約：底の quasicategory 性は不要。
使われ方：任意の底上の分類図式から元の全空間を同値まで復元する。 -/
lemma essentiallySmallLeftStraighteningComparison_isPrecompositionEquivalence {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (essentiallySmallLeftStraighteningComparison p hp) :=
  (essentiallySmallLeftStraighteningRepresentation p hp).isPrecompositionEquivalence

/-- 元の表現の存在は、その実際の全 Kan fiber が小さい Kan 模型を持つことを含意する。 -/
lemma LeftTransportRepresentation.hasEssentiallySmallFibers {E B : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers.of_fiber_equivalence p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection R.diagram)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.leftUnstraighteningProjection_hasSmallSimplexFibers R.diagram).essentiallySmall
    R.comparison R.over_base R.fiber_equivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportRepresentation (hasEssentiallySmallFibers)


/-- 同値不変な fiber の小ささは、実際の空間値 transport 表現の存在と正確に同値。 -/
lemma hasEssentiallySmallFibers_iff_transportRepresentation {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers p ↔ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) := by
  constructor
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.essentiallySmallLeftTransportRepresentation_nonempty p
  · rintro ⟨R⟩
    exact R.hasEssentiallySmallFibers

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
