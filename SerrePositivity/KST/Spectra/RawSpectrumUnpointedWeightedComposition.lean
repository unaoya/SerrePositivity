module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingCompositionLaws
public import SerrePositivity.KST.Spectra.RawSpectrumMappingFunctor
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorExchangeEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedSectionsParameters

/-!
概要：元の raw Hom の合成による、通常の weighted end の全 Hom パラメータの作用。
方針：後合成に自然な係数の合成を共有の weightedSectionsParameterMap に渡す。
規約：直積パラメータを用い、係数の元の合成を保持する。使われ方：点つき end の作用との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance parameterCompositionPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の raw Hom の合成を、右の Hom パラメータを持つ係数自然変換にする。 -/
def compositionParameterTransformation (X Y : OmegaSpectrum.{u}) :
    (pointedFunctor Y ⋙ PointedSimplicialSet.forget) ⋙
        tensorRight (space X Y.toKanSequence) ⟶
      pointedFunctor X ⋙ PointedSimplicialSet.forget where
  app Z := (β_ (space Y Z) (space X Y.toKanSequence)).hom ≫ composition X Y Z
  naturality Z T p := by
    change post Y p ▷ space X Y.toKanSequence ≫
      (β_ (space Y T) (space X Y.toKanSequence)).hom ≫ composition X Y T =
      ((β_ (space Y Z) (space X Y.toKanSequence)).hom ≫ composition X Y Z) ≫ post X p
    rw [BraidedCategory.braiding_naturality_left_assoc, ← id_tensorHom]
    erw [← composition_post]
    exact (Category.assoc _ _ _).symm

/-- 元の係数の合成を共有の weightedSectionsParameterMap で end の作用へ延長する。 -/
def unpointedWeightedComposition {I : Type u} [SmallCategory I]
    (X Y : OmegaSpectrum.{u}) (W : I ⥤ SSet.{u}) (D : I ⥤ KanSequence.{u}) :
    space X Y.toKanSequence ⊗
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W ((D ⋙ pointedFunctor Y) ⋙ PointedSimplicialSet.forget) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W ((D ⋙ pointedFunctor X) ⋙ PointedSimplicialSet.forget) :=
  (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap W
    (Functor.whiskerLeft D (compositionParameterTransformation X Y))

/-- 元の weighted end の作用は、各射影で係数の合成により評価される。 -/
lemma unpointedWeightedComposition_evaluation {I : Type u} [SmallCategory I]
    (X Y : OmegaSpectrum.{u})
    (W : I ⥤ SSet.{u}) (D : I ⥤ KanSequence.{u}) (i : I) :
    W.obj i ◁ unpointedWeightedComposition X Y W D ≫
        uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W ((D ⋙ pointedFunctor X) ⋙ PointedSimplicialSet.forget) i) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange (W.obj i) (space X Y.toKanSequence)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W ((D ⋙ pointedFunctor Y) ⋙ PointedSimplicialSet.forget))).hom ≫
        space X Y.toKanSequence ◁
          uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W ((D ⋙ pointedFunctor Y) ⋙ PointedSimplicialSet.forget) i) ≫
          composition X Y (D.obj i) := by
  rw [unpointedWeightedComposition, whiskerLeft_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsParameterMap_evaluation]
  change _ ◁ (β_ _ _).hom ≫ (α_ _ _ _).inv ≫
    _ ▷ _ ≫ (β_ (space Y (D.obj i)) (space X Y.toKanSequence)).hom ≫
      composition X Y (D.obj i) = _
  have h := congrArg (fun f ↦ f ≫ composition X Y (D.obj i))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_evaluation (W.obj i) (space X Y.toKanSequence) _ _
      (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W
        ((D ⋙ pointedFunctor Y) ⋙ PointedSimplicialSet.forget) i)))
  simp only [Category.assoc] at h
  exact h

end SerrePositivity.KST.Spectra.RawSpectrumMapping
