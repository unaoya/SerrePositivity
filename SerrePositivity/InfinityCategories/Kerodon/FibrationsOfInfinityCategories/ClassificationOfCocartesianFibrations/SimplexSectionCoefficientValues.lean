module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationBaseChangeConjugation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionCompNormalizedValue
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiagramIsoNormalizationAlgebra

/-!
概要：既存の共同切断比較の係数評価を、対象別切断図式の端点で読むための略記。
方針：元の評価と端点正規化をそのまま使う。
規約：新しい比較同型の選択や存在の入力を追加しない。
使われ方：Kerodon §5.6（Tag 027M）の指定底変換の合成則の計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.LimitsAndColimits.LimitsAndColimits
open Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance coefficientValues_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：元の対象別切断図式の略記。方針：既存の評価を使う。
規約：新しい対象を選ばない。使われ方：係数移送の式の端点を揃える。 -/
abbrev simplexSectionValue {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory B)) ⟶ SpaceInfinity.{u} :=
  kanDiagramCoherentNerve
    ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
      (leftFibrationObjectOf p))

/-- 概要：元の指定底変換の同じ係数評価を対象別図式の端点で読む略記。
方針：既存の後合成と端点正規化だけを使う。
規約：比較を選び直さない。使われ方：元の共役表示の係数計算。 -/
def simplexSectionBaseChangeCoefficient {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    FunctorIso (simplexSectionValue (pullback.snd p k))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
        simplexSectionValue p) :=
  diagramIsoCongr
    (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k,
      transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
    (by rw [Category.assoc, transportSimplexSectionInfinity_joint_evaluate p])
    (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k)
      (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))

/-- 概要：元の反復引き戻し比較の同じ係数値を読む略記。
方針：既存のKan値実現比較を使う。規約：標準比較の値を保持する。
使われ方：二段の底変換の補正因子。 -/
def simplexSectionCompositeCoefficient {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso (simplexSectionValue (pullback.snd p (l ≫ k)))
      (simplexSectionValue (pullback.snd (pullback.snd p k) l)) :=
  kanEnrichedRealizationValueIso
    (sectionBaseChangeCompComparison k l (transportSimplexDomainFunctor T))
    (sectionBaseChangeCompComparison_isQCatEquivalence k l (transportSimplexDomainFunctor T))
    (leftFibrationObjectOf p)

/-- 概要：底変換係数の略記は元の指定係数値と端点移送だけ異なる。
方針：正規化の異種等式を使う。規約：同じ値。
使われ方：貼り合わせの因子を略記へ戻す。 -/
lemma simplexSectionBaseChangeCoefficient_heq {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq (simplexSectionBaseChangeCoefficient p k)
      (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p))) :=
  diagramIsoCongr_heq _ _ _

/-- 概要：指定底変換の制限の共役表示を同じ係数値の略記で読む。
方針：端点正規化と逆同型・後合成の交換則を使う。
規約：元の指定底変換。使われ方：中間制限同型の相殺。 -/
lemma leftStraightening_baseChange_firstVertex_coefficient
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D)))
      ((leftClassificationSimplexIso p).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k))) ≪≫
        (simplexSectionBaseChangeCoefficient p k).symm ≪≫
        (leftClassificationSimplexIso (pullback.snd p k)).symm) := by
  simpa only [simplexSectionBaseChangeCoefficient, ← diagramIsoCongr_symm,
    ← functorIso_postcomp_symm] using
    leftStraighteningInfinityDiagram_baseChangeIso_firstVertex_conjugation p k

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
