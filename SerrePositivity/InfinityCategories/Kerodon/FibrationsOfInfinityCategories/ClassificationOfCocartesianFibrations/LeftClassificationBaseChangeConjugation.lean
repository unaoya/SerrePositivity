module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointRealizationComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationBaseChangeRestrictionFactorization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationRestrictionFactorValues
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationRestrictionPullbackValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationJointEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoChainTransport
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：指定分類底変換の初頂点制限を、同じ対象別制限同型による共役へ戻す。
方針：転置の頂点評価の既存の式と、元の実現の頂点表示を使う。
規約：図式全体の写像を比較する。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の三因子の端点正規化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Project.QuasicategoryAuxiliaries
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance baseChangeConjugation_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

private lemma isoTransThree_heq {L : Type v} [Category.{w} L]
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : L}
    (e₁ : a₀ ≅ a₁) (e₂ : a₁ ≅ a₂) (e₃ : a₂ ≅ a₃)
    (d₁ : b₀ ≅ b₁) (d₂ : b₁ ≅ b₂) (d₃ : b₂ ≅ b₃)
    (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃)
    (he₁ : HEq e₁ d₁) (he₂ : HEq e₂ d₂) (he₃ : HEq e₃ d₃) :
    HEq (e₁ ≪≫ e₂ ≪≫ e₃) (d₁ ≪≫ d₂ ≪≫ d₃) := by
  subst b₀ b₁ b₂ b₃
  cases eq_of_heq he₁
  cases eq_of_heq he₂
  cases eq_of_heq he₃
  rfl

/-- 概要：指定底変換の初頂点制限は元の対象別制限同型による指定切断比較の共役。
方針：元の三因子の同じ係数値を前後合成の法則で正規化する。
規約：指定底変換も切断比較も選び直さない。使われ方：二段底変換の中間制限同型の消去。
対応：Kerodon §5.6（Tag 027M）、分類の底変換の既存構成の法則。 -/
lemma leftStraighteningInfinityDiagram_baseChangeIso_firstVertex_conjugation
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor k))
    let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
    HEq ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        (U.map (transportSimplexFirstVertexMap D)))
      ((leftClassificationSimplexIso p).precomp t ≪≫
        diagramIsoCongr
          (by rw [Category.assoc, transportSimplexSectionInfinity_joint_evaluate p])
          (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k,
            transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
          (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k).symm evp) ≪≫
        (leftClassificationSimplexIso (pullback.snd p k)).symm) := by
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor k))
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
  have h₀ : (t ≫ (U.map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningSectionJointDiagram B)) ≫ evp =
      t ≫ (U.map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningInfinityDiagram p) := by
    rw [Category.assoc, Category.assoc, leftStraighteningInfinityDiagram_joint_evaluate p]
  have h₁ : (t ≫ transportSimplexSectionInfinity B) ≫ evp =
      t ≫ kanDiagramCoherentNerve
        ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
          (leftFibrationObjectOf p)) := by
    rw [Category.assoc, transportSimplexSectionInfinity_joint_evaluate p]
  have h₂ : (transportSimplexSectionInfinity D ≫ P) ≫ evp =
      kanDiagramCoherentNerve
        ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate
          (leftFibrationObjectOf (pullback.snd p k))) := by
    rw [Category.assoc, leftFibrationBaseChange_evaluate p k,
      transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)]
  have h₃ : ((U.map (transportSimplexFirstVertexMap D) ≫
        leftStraighteningSectionJointDiagram D) ≫ P) ≫ evp =
      U.map (transportSimplexFirstVertexMap D) ≫
        leftStraighteningInfinityDiagram (pullback.snd p k) := by
    rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
      leftStraighteningInfinityDiagram_joint_evaluate (pullback.snd p k)]
  let e₂ := FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k).symm evp
  have h := isoTransThree_heq
    (FunctorIso.postcomp ((leftStraighteningSectionJointDiagram_restrictIso B).precomp t) evp)
    e₂
    (FunctorIso.postcomp ((leftStraighteningSectionJointDiagram_restrictIso D).postcomp P).symm
      evp)
    ((leftClassificationSimplexIso p).precomp t)
    (diagramIsoCongr h₁ h₂ e₂)
    (leftClassificationSimplexIso (pullback.snd p k)).symm
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) h₀)
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) h₁)
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) h₂)
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) h₃)
    (leftClassificationSimplexIso_precomp_heq_joint p t)
    (diagramIsoCongr_heq h₁ h₂ e₂).symm
    (leftClassificationSimplexIso_pullback_symm_heq_joint p k)
  exact (leftStraighteningInfinityDiagram_baseChangeIso_firstVertex_factors p k).trans h

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
