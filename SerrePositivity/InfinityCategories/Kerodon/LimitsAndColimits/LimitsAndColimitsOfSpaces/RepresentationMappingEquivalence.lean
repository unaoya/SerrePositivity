module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationFamilyComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningMappingEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorComparisonEquivalence

/-!
概要：小さい次数 fiber の一般の表現の写像空間比較射は同値。
方針：比較射と unstraightening と始域前合成の合成を標的後合成と同型にする。
規約：底は ∞ 圏、次数 fiber の小ささを明示する。
使われ方：一般の straightening の写像空間の完全忠実性への入力。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：一般の二表現の相対写像空間から分類図式の変換空間への比較射は同値。
方針：前後合成の同値性と unstraightening の比較の同値性を可換式で消去する。
規約：底の quasicategory 性以外に全空間の充填性や小ささを要求しない。
使われ方：選択した分類の写像空間上の完全忠実性。 -/
lemma transportRepresentationMappingSpaceMap_isQCatEquivalence {E F B : SSet.{u + 1}}
    [Quasicategory B] {p : E ⟶ B} {q : F ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers q)
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportRepresentationMappingSpaceMap hp hq R S) := by
  have hpost := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection S.diagram) S.comparison S.over_base
    S.isPrecompositionEquivalence p
  let a : Over.mk p ⟶ Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection R.diagram) :=
    Over.homMk R.comparison R.over_base
  have hpre := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection S.diagram) a R.isPrecompositionEquivalence
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap_isQCatEquivalence R.diagram S.diagram
  have he := hpost.ofFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRepresentationMappingSpaceMap_comparisonIso hp hq R S).symm
  exact (hu.comp hpre).cancel_right he

/-- 概要：小さい次数 fiber の選択分類の実際の写像空間比較は同値。
方針：選択した二表現に一般の同値性を適用する。
規約：比較射を同値な別の射へ置き換えない。
使われ方：straightening の選択分類の完全忠実性の写像空間での検証。 -/
lemma smallFiberLeftStraighteningMappingSpaceMap_isQCatEquivalence {E F B : SSet.{u + 1}}
    [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.smallFiberLeftStraighteningMappingSpaceMap p q hp hq) :=
  transportRepresentationMappingSpaceMap_isQCatEquivalence hp hq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallFiberLeftStraighteningRepresentation p hp)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallFiberLeftStraighteningRepresentation q hq)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
