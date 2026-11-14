module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionBaseChangeValuePasting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationRestrictionPullbackValue
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiagramIsoNormalizationAlgebra

/-!
概要：同じ係数での三因子の貼り合わせを、元の標準引き戻し対象の切断図式へ正規化する。
方針：共同貼り合わせの同じ係数値と、端点正規化の合成則を使う。
規約：生の係数比較と直接底変換を同じ指定値として保持する。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の合成則。
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
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance coefficientPasting_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

private lemma normalizedTriple_heq {A X : SSet.{u}}
    {f₀ f₁ f₂ f₃ f₄ g₀ g₁ g₂ g₃ g₄ : A ⟶ X}
    (e₁ : FunctorIso f₀ f₁) (e₂ : FunctorIso f₁ f₂) (e₃ : FunctorIso f₂ f₃)
    (d : FunctorIso f₀ f₄) (h : HEq (e₁ ≪≫ e₂ ≪≫ e₃) d)
    (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) (h₂ : f₂ = g₂)
    (h₃ : f₃ = g₃) (h₄ : f₄ = g₄) :
    HEq (diagramIsoCongr h₀ h₁ e₁ ≪≫ diagramIsoCongr h₁ h₂ e₂ ≪≫
        diagramIsoCongr h₂ h₃ e₃) (diagramIsoCongr h₀ h₄ d) := by
  exact (diagramIsoCongr_trans_three h₀ h₁ h₂ h₃ e₁ e₂ e₃).symm.heq.trans
    ((diagramIsoCongr_heq h₀ h₃ (e₁ ≪≫ e₂ ≪≫ e₃)).trans
      (h.trans (diagramIsoCongr_heq h₀ h₄ d).symm))

/-- 概要：同じ全単体の三因子の係数貼り合わせは元の対象別切断図式の端点でも成立。
方針：評価の元の式で四端点を揃え、同じ三因子の正規化の合成則を使う。
規約：指定三因子と直接底変換を保持する。使われ方：分類底変換の共役の中間因子の相殺。 -/
lemma simplexSectionCoefficient_pasting {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor l))
    let s := U.map (nerveMap (transportSimplexFunctor k))
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
    let S₀ := kanDiagramCoherentNerve
      ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor T)).evaluate
        (leftFibrationObjectOf q₀))
    let S₁ := kanDiagramCoherentNerve
      ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor T)).evaluate
        (leftFibrationObjectOf q₁))
    let S₂ := t ≫ kanDiagramCoherentNerve
      ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate
        (leftFibrationObjectOf (pullback.snd p k)))
    let S₃ := t ≫ (s ≫ kanDiagramCoherentNerve
      ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
        (leftFibrationObjectOf p)))
    let γ := diagramIsoCongr (f' := S₀) (g' := S₁)
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p (l ≫ k),
        transportSimplexSectionInfinity_joint_evaluate q₀])
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k, Category.assoc,
        leftFibrationBaseChange_evaluate (pullback.snd p k) l,
        transportSimplexSectionInfinity_joint_evaluate q₁])
      (FunctorIso.postcomp (simplexSectionCompIso k l) evp)
    let δ₁ := diagramIsoCongr (f' := S₁) (g' := S₂)
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k, Category.assoc,
        leftFibrationBaseChange_evaluate (pullback.snd p k) l,
        transportSimplexSectionInfinity_joint_evaluate q₁])
      (by rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
      (FunctorIso.postcomp (simplexSectionFirstIso k l) evp)
    let δ₂ := diagramIsoCongr (f' := S₂) (g' := S₃)
      (by rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
      (by rw [Category.assoc, Category.assoc, transportSimplexSectionInfinity_joint_evaluate p])
      (FunctorIso.postcomp (simplexSectionSecondIso k l) evp)
    let δ := diagramIsoCongr (f' := S₀)
      (g' := U.map (nerveMap (transportSimplexFunctor (l ≫ k))) ≫
        kanDiagramCoherentNerve
          ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
            (leftFibrationObjectOf p)))
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p (l ≫ k),
        transportSimplexSectionInfinity_joint_evaluate q₀])
      (by rw [Category.assoc, transportSimplexSectionInfinity_joint_evaluate p])
      (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso (l ≫ k)) evp)
    HEq (γ ≪≫ δ₁ ≪≫ δ₂) δ := by
  dsimp only
  exact normalizedTriple_heq _ _ _ _ (simplexSectionBaseChange_value_pasting p k l) _ _ _ _ _

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
