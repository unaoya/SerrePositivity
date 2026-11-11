module

public import SerrePositivity.KST.Spectra.SpectrumCotensorCompatibleMaps
public import SerrePositivity.KST.Spectra.SpectrumPointedEnrichment
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterSquares

/-!
概要：cotensor の普遍評価と可換な射の組の合成。
方針：内部 Hom の等式を評価の正方形へ移し、パラメータ付き正方形の合成を使う。
規約：全 smash パラメータでの合成。使われ方：coherent な cotensor 関手化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
local instance compatibleCompositionPointedEnrichment :
    EnrichedCategory PointedSimplicialSet.{u} OmegaSpectrum.{u} := pointedEnrichment

/-- 内部 Hom での可換条件は、パラメータ付きの評価の正方形と同値。 -/
lemma condition_iff (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u})
    {T : PointedSimplicialSet.{u}}
    (f : T ⟶ RawSpectrumMapping.pointedSpace X Y.toKanSequence)
    (g : T ⟶ RawSpectrumMapping.pointedSpace (cotensor A X) (cotensor A Y).toKanSequence) :
    g ≫ cotensorEvaluationPrecomposition (cotensor A X) Y A = f ≫ evaluationPost A X Y ↔
      (cotensorEvaluation A X ⊗ₘ f) ≫
          RawSpectrumMapping.pointedComposition (cotensor A X) X Y.toKanSequence =
        (β_ A T).hom ≫ (g ⊗ₘ cotensorEvaluation A Y) ≫
          RawSpectrumMapping.pointedComposition (cotensor A X) (cotensor A Y) Y.toKanSequence := by
  have hpre : uncurry (g ≫ cotensorEvaluationPrecomposition (cotensor A X) Y A) =
      (β_ A T).hom ≫ (g ⊗ₘ cotensorEvaluation A Y) ≫
        RawSpectrumMapping.pointedComposition (cotensor A X) (cotensor A Y)
          Y.toKanSequence := by
    rw [uncurry_natural_left, cotensorEvaluationPrecomposition, uncurry_curry,
      BraidedCategory.braiding_naturality_right_assoc, ← tensorHom_def_assoc]
  have hpost : uncurry (f ≫ evaluationPost A X Y) =
      (cotensorEvaluation A X ⊗ₘ f) ≫
        RawSpectrumMapping.pointedComposition (cotensor A X) X Y.toKanSequence := by
    rw [uncurry_natural_left, evaluationPost, uncurry_curry, ← tensorHom_def'_assoc]
  constructor
  · intro h
    have hh := congrArg uncurry h
    rw [hpre, hpost] at hh
    exact hh.symm
  · intro h
    apply uncurry_injective
    rw [hpre, hpost]
    exact h.symm

/-- 段ごとに合成した二つの射影も普遍評価と可換。 -/
lemma composition_condition (A : PointedSimplicialSet.{u}) (X Y Z : OmegaSpectrum.{u}) :
    (cotensorMap A X Y ⊗ₘ cotensorMap A Y Z) ≫
        RawSpectrumMapping.pointedComposition (cotensor A X) (cotensor A Y)
          (cotensor A Z).toKanSequence ≫ cotensorEvaluationPrecomposition (cotensor A X) Z A =
      (sourceMap A X Y ⊗ₘ sourceMap A Y Z) ≫
        RawSpectrumMapping.pointedComposition X Y Z.toKanSequence ≫ evaluationPost A X Z := by
  rw [← Category.assoc, ← Category.assoc]
  apply (condition_iff A X Z _ _).mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_square_comp PointedSimplicialSet.{u}
    (C := OmegaSpectrum.{u}) (A := A) (P := pointedSpace A X Y) (Q := pointedSpace A Y Z)
    (X := X) (Y := Y) (Z := Z)
    (X' := cotensor A X) (Y' := cotensor A Y) (Z' := cotensor A Z)
    (cotensorEvaluation A X) (cotensorEvaluation A Y) (cotensorEvaluation A Z)
    (sourceMap A X Y) (cotensorMap A X Y) (sourceMap A Y Z) (cotensorMap A Y Z)
    ((condition_iff A X Y _ _).mp (condition A X Y))
    ((condition_iff A Y Z _ _).mp (condition A Y Z))

/-- 可換な組をそれぞれの射影で合成する。 -/
def composition (A : PointedSimplicialSet.{u}) (X Y Z : OmegaSpectrum.{u}) :
    pointedSpace A X Y ⊗ pointedSpace A Y Z ⟶ pointedSpace A X Z :=
  pullback.lift
    ((cotensorMap A X Y ⊗ₘ cotensorMap A Y Z) ≫
      RawSpectrumMapping.pointedComposition (cotensor A X) (cotensor A Y)
        (cotensor A Z).toKanSequence)
    ((sourceMap A X Y ⊗ₘ sourceMap A Y Z) ≫
      RawSpectrumMapping.pointedComposition X Y Z.toKanSequence)
    (composition_condition A X Y Z)

@[reassoc (attr := simp)]
lemma composition_sourceMap (A : PointedSimplicialSet.{u}) (X Y Z : OmegaSpectrum.{u}) :
    composition A X Y Z ≫ sourceMap A X Z =
      (sourceMap A X Y ⊗ₘ sourceMap A Y Z) ≫
        RawSpectrumMapping.pointedComposition X Y Z.toKanSequence :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma composition_cotensorMap (A : PointedSimplicialSet.{u}) (X Y Z : OmegaSpectrum.{u}) :
    composition A X Y Z ≫ cotensorMap A X Z =
      (cotensorMap A X Y ⊗ₘ cotensorMap A Y Z) ≫
        RawSpectrumMapping.pointedComposition (cotensor A X) (cotensor A Y)
          (cotensor A Z).toKanSequence :=
  pullback.lift_fst _ _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
