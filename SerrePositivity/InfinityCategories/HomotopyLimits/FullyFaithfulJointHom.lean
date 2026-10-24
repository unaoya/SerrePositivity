module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.HomotopyLimits.TwistedArrowFunctorComparison
public import SerrePositivity.InfinityCategories.F2.Compact.ClassificationTransport
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorSpaceCurrying
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps

/-!
概要：充満忠実な元の関手は、元の共同 Hom・全 Yoneda 図式を全自然同型で保つ。
方針：実際の twisted arrow 比較の全 fiber 同値性を分類し、同じ両変数で展開する。
規約：全図式と元の関手を保持し、対象対ごとの同値で自然性を代用しない。
使われ方：Yoneda 像上の共同図式比較と、密度による大域 Yoneda 評価比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Compact
local instance {X : SSet.{u}} [Quasicategory X] : Quasicategory (X.op ⊗ X) :=
  quasicategory_of_innerFibration (CartesianMonoidalCategory.fst X.op X)

/-- 充満忠実な元の関手の実際の twisted arrow 比較を分類した、全図式の自然同型。 -/
def twistedArrowHomInfinity_fullyFaithfulIso {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsFullyFaithful f) :
    FunctorIso (twistedArrowHomInfinity C)
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f ⊗ₘ f) ≫
        twistedArrowHomInfinity D) := by
  have : LeftFibration (pullback.snd (twistedArrowProjection D) (SSet.opFunctor.map f ⊗ₘ f)) :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := twistedArrowProjection D))⟩
  exact leftClassification_of_precompositionEquivalence _ _
    (twistedArrowFunctorComparison f) (twistedArrowFunctorComparison_projection f)
    (twistedArrowFunctorComparison_isPrecompositionEquivalence f hf) ≪≫
      (leftStraighteningInfinityDiagram_baseChangeIso (twistedArrowProjection D)
        (SSet.opFunctor.map f ⊗ₘ f)).symm

/-- 元の両変数の底写像の宇宙比較は、同じ元の関手の両作用と厳密に可換。 -/
lemma jointHomBaseMap_naturality {C D : SSet.{u}} (f : C ⟶ D) :
    (uliftTensorIso.{u, u + 1} C.op C).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f ⊗ₘ f) =
    ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f) ⊗ₘ
      (SSet.uliftFunctor.{u + 1, u}).map f) ≫ (uliftTensorIso D.op D).inv := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 充満忠実な元の関手は、同じ全二変数の共同 Hom 図式を自然同型で保つ。 -/
def homInfinityJoint_fullyFaithfulIso {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsFullyFaithful f) :
    FunctorIso (homInfinityJointEvaluation C)
      (((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f) ⊗ₘ
        (SSet.uliftFunctor.{u + 1, u}).map f) ≫ homInfinityJointEvaluation D) := by
  have e := (twistedArrowHomInfinity_fullyFaithfulIso f hf).precomp
    (uliftTensorIso.{u, u + 1} C.op C).inv
  change FunctorIso (homInfinityJointEvaluation C)
    ((uliftTensorIso C.op C).inv ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f ⊗ₘ f) ≫
        twistedArrowHomInfinity D)) at e
  rw [← Category.assoc, jointHomBaseMap_naturality, Category.assoc] at e
  exact e

/-- 充満忠実な元の関手の全 Yoneda 後合成と元の全前層制限は、全自然同型で元を回収。 -/
def yonedaInfinityMap_fullyFaithfulRestrictionIso {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsFullyFaithful f) :
    FunctorIso (yonedaInfinityMap C)
      ((SSet.uliftFunctor.{u + 1, u}).map f ≫ yonedaInfinityMap D ≫
        presheafInfinityRestriction f) := by
  have hr : uncurry ((SSet.uliftFunctor.{u + 1, u}).map f ≫ yonedaInfinityMap D ≫
      presheafInfinityRestriction f) =
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f) ⊗ₘ
        (SSet.uliftFunctor.{u + 1, u}).map f) ≫ homInfinityJointEvaluation D := by
    dsimp only [presheafInfinityRestriction]
    rw [← Category.assoc, uncurry_pre_app, uncurry_natural_left, yonedaInfinityMap_uncurry]
    apply SSet.hom_ext
    intro n
    rfl
  have e := FunctorIso.curry (homInfinityJoint_fullyFaithfulIso f hf)
  rw [← hr, curry_uncurry] at e
  exact e

end SerrePositivity.InfinityCategories.HomotopyLimits
