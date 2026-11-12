module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwistedHomEndSection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.PullbackSections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityEquivalence

/-!
概要：end の切断空間を二変数の Hom 図式間の写像空間へ移す。
方針：切断を相対関手空間へ戻し、底変換と left fibration 分類の充満忠実性を使う。
規約：元の二関手と実際の Hom 射影の pullback を保持する。
使われ方：P-12 の写像空間の end 比較を Yoneda の普遍性へ接続する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

local instance supplyEndSectionsRelativeHom_productQuasicategory
    {A : SSet.{u}} [Quasicategory A] : Quasicategory (A.op ⊗ A) :=
  quasicategory_of_innerFibration (fst A.op A)

local instance supplyEndSectionsRelativeHom_sectionsKanComplex
    {A C : SSet.{u}} [Quasicategory C] (F G : A ⟶ C) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex _

/-- 概要：二関手の反変・共変な両変数をまとめた底写像。
方針：F の反転と G の直積を取る。
規約：始域は元の A の二変数全体。使われ方：Hom の二変数図式の底変換。 -/
def functorHomBifunctorBase {A C : SSet.{u}} (F G : A ⟶ C) : A.op ⊗ A ⟶ C.op ⊗ C :=
  SSet.opFunctor.map F ⊗ₘ G

/-- 概要：twisted arrow への両端制限は二変数全体の底写像の制限。
方針：左右の射影の定義を比較する。
規約：射の厳密な等式。使われ方：相対関手空間の底変換。 -/
lemma functorEndPairBase_bifunctor {A C : SSet.{u}} (F G : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection A ≫ functorHomBifunctorBase F G = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndPairBase F G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：二関手の共同 Hom を元の二変数上に分類する全空間。
方針：C の Hom 射影を F の反転と G の積で引き戻す。
規約：底を A の二変数全体とする。使われ方：Hom_A からの相対写像空間。 -/
def functorHomBifunctorTotal {A C : SSet.{u}} (F G : A ⟶ C) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (functorHomBifunctorBase F G)

/-- 概要：二変数上の Hom の分類全空間の射影。
方針：実 pullback の第二射影を使う。
規約：元の二変数を保持する。使われ方：left fibration 分類の入力。 -/
def functorHomBifunctorProjection {A C : SSet.{u}} (F G : A ⟶ C) :
    functorHomBifunctorTotal F G ⟶ A.op ⊗ A :=
  pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (functorHomBifunctorBase F G)

/-- 概要：共同 Hom の二変数への底変換も left fibration。
方針：元の twisted arrow 射影の pullback 安定性を使う。
規約：A の quasicategory 性はこの段階では不要。
使われ方：二変数図式の相対 Hom の Kan 性。 -/
instance functorHomBifunctorProjection_leftFibration {A C : SSet.{u}} [Quasicategory C]
    (F G : A ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (functorHomBifunctorProjection F G) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C))⟩

/-- 概要：end 切断は Hom_A から二関手の Hom への相対関手空間と厳密に同型。
方針：切断の相対関手表示と二段の pullback の底変換同型を合成する。
規約：単なる各頂点の対応に弱めない。使われ方：分類同値による二変数 Hom への移送。 -/
def functorEndSectionsRelativeHomIso {A C : SSet.{u}} (F G : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (functorHomBifunctorProjection F G) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.pullbackSectionsRelativeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndPairBase F G) ≪≫
    eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C))
      (functorEndPairBase_bifunctor F G).symm) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
      (functorHomBifunctorBase F G) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection A)).symm

/-- 概要：left fibrations の相対 Hom は元の分類図式間の全自然変換空間と同値。
方針：豊穣 Hom の coherent 比較に、元の分類写像の充満忠実性を合成する。
規約：既存の分類写像そのものを使う。使われ方：end の二変数の分類図式間への移送。 -/
def relativeHomStraighteningEquivalence {E E' B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : E' ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram q))) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityMappingEquivalence p q).trans
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isFullyFaithful B)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityVertex p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityVertex q)).isQCatEquivalence.choose)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_vertex] using e

/-- 概要：end 切断の持ち上げは二変数 Hom の分類図式間の写像空間と同値。
方針：相対関手空間の厳密な同型を宇宙変更し、分類の Hom 同値を適用する。
規約：元の Hom_A と共同 Hom の底変換を始点・終点に固定する。
使われ方：P-12 の end 比較を Yoneda の変換空間へ読む入口。 -/
def functorEndSectionsBifunctorHomEquivalence
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C] (F G : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity A))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (functorHomBifunctorProjection F G)))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso
    (functorEndSectionsRelativeHomIso F G))).trans
      (relativeHomStraighteningEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection A)
        (functorHomBifunctorProjection F G))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
