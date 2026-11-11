module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SmallCoherentStraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorPostEquivalence

/-!
概要：小さい全空間の復元の比較を実際の相対写像空間の同値へ移す。
方針：元の全空間の比較で前合成・後合成し前合成側の逆を選ぶ。
規約：coherent 変換からの既存の比較射の同値性とは区別する。
使われ方：一般の straightening の写像空間の比較を復元した対象へ運ぶ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：元の射影から分類図式の unstraightening への底上の比較。
方針：既証明の比較と射影の可換性を底上の射へ束ねる。
規約：全空間の実際の射を取る。
使われ方：相対写像空間の前合成。 -/
def smallLeftStraighteningOverComparison {E B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    Over.mk p ⟶ Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningDiagram p)) :=
  Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningComparison p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningComparison_over_base p)

/-- 概要：元の全空間の比較による相対写像空間の前合成。
方針：分類した始域からの相対関手を元の始域へ制限する。
規約：標的の射影は任意。
使われ方：実際の写像空間の始域側の復元。 -/
def smallLeftStraighteningMappingPre {E X B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : X ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningDiagram p)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q (smallLeftStraighteningOverComparison p)

/-- 概要：復元の比較による前合成は実際の相対写像空間の同値。
方針：全空間の前合成同値を底上の相対関手空間へ移す。
規約：底は quasicategory、標的は left fibration。
使われ方：写像空間上の復元の逆比較。 -/
lemma smallLeftStraighteningMappingPre_isQCatEquivalence {E X B : SSet.{u + 1}}
    [Quasicategory B] [∀ m, Small.{u} (E.obj m)]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (smallLeftStraighteningMappingPre p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence q (smallLeftStraighteningOverComparison p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningComparison_isPrecompositionEquivalence p)

/-- 概要：元の全空間の比較による相対写像空間の後合成。
方針：元の終域への相対関手を分類した終域への相対関手へ送る。
規約：定義域の構造射は任意。
使われ方：実際の写像空間の終域側の復元。 -/
def smallLeftStraighteningMappingPost {E A B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningDiagram p)) a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningDiagram p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningComparison p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningComparison_over_base p) a

/-- 概要：復元の比較による後合成は実際の相対写像空間の同値。
方針：底上の逆射と相対単位・余単位による後合成の判定を使う。
規約：底は quasicategory。
使われ方：写像空間上の復元の順比較。 -/
lemma smallLeftStraighteningMappingPost_isQCatEquivalence {E A B : SSet.{u + 1}}
    [Quasicategory B] [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (a : A ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (smallLeftStraighteningMappingPost p a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningDiagram p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningComparison p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningComparison_over_base p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningComparison_isPrecompositionEquivalence p) a

/-- 概要：元の二つの left fibration の相対写像空間を復元した二対象の写像空間へ送る。
方針：始域の比較の前合成の逆と終域の比較の後合成を続ける。
規約：ここでは写像空間ごとの射であり全対象にわたる関手性はまだ含めない。
使われ方：coherent な分類への写像空間比較の中間射。 -/
def smallStraighteningReconstructionMappingSpaceMap {E X B : SSet.{u + 1}}
    [Quasicategory B] [∀ m, Small.{u} (E.obj m)] [∀ m, Small.{u} (X.obj m)]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningDiagram q))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningDiagram p)) :=
  (smallLeftStraighteningMappingPre_isQCatEquivalence p q).choose.inv ≫
    smallLeftStraighteningMappingPost q
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningDiagram p))

/-- 概要：実際の相対写像空間と復元した二対象の相対写像空間の比較は同値。
方針：前合成の逆の同値性と後合成の同値性を合成する。
規約：coherent な変換の写像空間との比較は後続の課題。
使われ方：元の left fibration の写像空間を一般の分類へ運ぶ。 -/
lemma smallStraighteningReconstructionMappingSpaceMap_isQCatEquivalence
    {E X B : SSet.{u + 1}} [Quasicategory B]
    [∀ m, Small.{u} (E.obj m)] [∀ m, Small.{u} (X.obj m)]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (smallStraighteningReconstructionMappingSpaceMap p q) :=
  (smallLeftStraighteningMappingPre_isQCatEquivalence p q).choose.symm.isQCatEquivalence.comp
    (smallLeftStraighteningMappingPost_isQCatEquivalence q
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallLeftStraighteningDiagram p)))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
