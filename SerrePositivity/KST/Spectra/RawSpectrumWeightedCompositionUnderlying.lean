module

public import SerrePositivity.KST.Spectra.RawSpectrumWeightedComposition
public import SerrePositivity.KST.Spectra.RawSpectrumPointedCompositionComparison
public import SerrePositivity.KST.Spectra.FreePointedHomStrength
public import SerrePositivity.KST.Spectra.RawSpectrumUnpointedWeightedComposition

/-!
概要：元の点つき weighted Hom end の作用を忘れると、共有の weighted end の作用に一致。
方針：自由基点の内部 Hom の評価公式と、各 end 射影の係数の合成の一致を使う。
規約：元の作用を別の作用へ取り替えず、全直積パラメータで照合する。
使われ方：BF Hom 比較の豊穣自然性を γ3 の元の weighted end へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance weightedActionForgetSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 点つき weighted Hom end の作用を忘れた射の、元の係数での評価公式。 -/
lemma weightedComposition_underlying_evaluation {I : Type u} [SmallCategory I]
    (X Y : OmegaSpectrum.{u})
    (W : I ⥤ SSet.{u}) (D : I ⥤ KanSequence.{u}) (i : I) :
    uncurry (PointedSimplicialSet.productToSmash (pointedSpace X Y.toKanSequence)
        (PointedWeightedEnd.obj W (D ⋙ pointedFunctor Y)) ≫
      (weightedComposition X Y W D).right ≫
        (end_.π (PointedWeightedEnd.diagram W (D ⋙ pointedFunctor X)) i).right ≫
          FreePointedHomRestriction.restrict (W.obj i) (pointedSpace X (D.obj i))) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange (W.obj i) (space X Y.toKanSequence)
        (PointedWeightedEnd.obj W (D ⋙ pointedFunctor Y)).right).hom ≫
        space X Y.toKanSequence ◁
          uncurry ((end_.π (PointedWeightedEnd.diagram W (D ⋙ pointedFunctor Y)) i).right ≫
            FreePointedHomRestriction.restrict (W.obj i) (pointedSpace Y (D.obj i))) ≫
            composition X Y (D.obj i) := by
  erw [← Category.assoc (weightedComposition X Y W D).right,
    ← Under.comp_right, weightedComposition_π]
  have h := FreePointedHomRestriction.strength_evaluation_parameter (W.obj i)
    (pointedSpace X Y.toKanSequence) (pointedSpace Y (D.obj i)) (pointedSpace X (D.obj i))
    (PointedWeightedEnd.obj W (D ⋙ pointedFunctor Y))
    (end_.π (PointedWeightedEnd.diagram W (D ⋙ pointedFunctor Y)) i)
    (pointedComposition X Y (D.obj i))
  rw [productToSmash_pointedComposition] at h
  exact h
/-- 元の weighted end の作用は、点つき end の忘却同型の後も同じ係数で評価される。 -/
lemma unpointedWeightedComposition_underlyingIso_evaluation {I : Type u} [SmallCategory I]
    (X Y : OmegaSpectrum.{u})
    (W : I ⥤ SSet.{u}) (D : I ⥤ KanSequence.{u}) (i : I) :
    uncurry ((𝟙 (space X Y.toKanSequence) ⊗ₘ
        (PointedWeightedEnd.underlyingIso W (D ⋙ pointedFunctor Y)).hom) ≫
      unpointedWeightedComposition X Y W D ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W ((D ⋙ pointedFunctor X) ⋙ PointedSimplicialSet.forget) i) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange (W.obj i) (space X Y.toKanSequence)
        (PointedWeightedEnd.obj W (D ⋙ pointedFunctor Y)).right).hom ≫
        space X Y.toKanSequence ◁
          uncurry ((end_.π (PointedWeightedEnd.diagram W (D ⋙ pointedFunctor Y)) i).right ≫
            FreePointedHomRestriction.restrict (W.obj i) (pointedSpace Y (D.obj i))) ≫
            composition X Y (D.obj i) := by
  rw [id_tensorHom, uncurry_natural_left, uncurry_natural_left,
    unpointedWeightedComposition_evaluation, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  have h := congrArg uncurry (PointedWeightedEnd.underlyingIso_π W (D ⋙ pointedFunctor Y) i)
  rw [uncurry_natural_left] at h
  rw [← whiskerLeft_comp_assoc (space X Y.toKanSequence), h]
  rfl

/-- 元の点つき end の合成作用は、忘却同型を通して共有の weighted end の作用と一致。 -/
lemma weightedComposition_underlyingIso {I : Type u} [SmallCategory I]
    (X Y : OmegaSpectrum.{u}) (W : I ⥤ SSet.{u}) (D : I ⥤ KanSequence.{u}) :
    PointedSimplicialSet.productToSmash (pointedSpace X Y.toKanSequence)
        (PointedWeightedEnd.obj W (D ⋙ pointedFunctor Y)) ≫
      (weightedComposition X Y W D).right ≫
        (PointedWeightedEnd.underlyingIso W (D ⋙ pointedFunctor X)).hom =
      (𝟙 (space X Y.toKanSequence) ⊗ₘ
        (PointedWeightedEnd.underlyingIso W (D ⋙ pointedFunctor Y)).hom) ≫
          unpointedWeightedComposition X Y W D := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  apply uncurry_injective
  conv_lhs => rw [Category.assoc, Category.assoc, PointedWeightedEnd.underlyingIso_π]
  conv_rhs => rw [Category.assoc]
  exact (weightedComposition_underlying_evaluation X Y W D i).trans
    (unpointedWeightedComposition_underlyingIso_evaluation X Y W D i).symm

end SerrePositivity.KST.Spectra.RawSpectrumMapping
