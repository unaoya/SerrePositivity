module

public import SerrePositivity.KST.Spectra.TracedOriginalLoopRawInterval
public import SerrePositivity.KST.Spectra.RawSpectrumParameterRestriction
public import SerrePositivity.KST.Spectra.RawSpectrumPointedUnits
public import SerrePositivity.KST.Spectra.PointedPrecompositionInterval

/-!
概要：元の源比較の全 Hom 区間を恒等射で評価し、源単位自身の実区間へ戻す。
方針：同じ全 Hom 区間の段評価・単位評価を使い、転置後に単位で評価する。
規約：段ごとに区間を選び直さない。使われ方：実評価の源比較を通る段区間の指定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open RawSpectrumMapping

/-- 転置した単位族を単位で評価すると、元の射へ戻る。 -/
lemma transpose_curry'_unit {W V : PointedSimplicialSet.{u}} (f : W ⟶ V) :
    PointedMapping.transpose (curry' f) ≫ (unitIsoSelf (X := V)).hom = f := by
  apply curry'_injective
  rw [← PointedMapping.transpose_unit, PointedMapping.transpose_transpose]

/-- 同じ全 Hom 区間を恒等射で評価した、源比較自身の元の単位族。 -/
def tracedOriginalLoopRawComparison_unit_interval (X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom (X.level n).space
        ((KanSequence.signedLoopTail X.toKanSequence).level n).space))
      (curry' ((tracedOriginalLoopRawComparison X).app n))
      (curry' ((tracedSignedLoopUnit X).app n ≫ (signedLoopProjection X).app n)) := by
  let P := (tracedOriginalLoopRawComparison_stage_interval X X n).pre (pointedIdentity X)
  have he (f : (X.level n).space ⟶
      ((KanSequence.signedLoopTail X.toKanSequence).level n).space) :
      curry' f = pointedIdentity X ≫
        (pointedEvaluation X X.toKanSequence n ≫ (ihom (X.level n).space).map f) := by
    rw [← Category.assoc, pointedIdentity_evaluation, curry'_ihom_map, Category.id_comp]
  exact P.changeEndpoints (he _) (he _)

/-- 元の同じ全 Hom 区間から得た、raw 源比較とトレース付き単位の射影の実区間。 -/
def tracedOriginalLoopRawComparison_level_interval (X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint ((KanSequence.signedLoopTail X.toKanSequence).level n).space)
      ((tracedOriginalLoopRawComparison X).app n)
      ((tracedSignedLoopUnit X).app n ≫ (signedLoopProjection X).app n) :=
  PointedMapping.VerticalPath.changeEndpoints
    (((tracedOriginalLoopRawComparison_unit_interval X n).basedTranspose).basedPost
      (unitIsoSelf (X := ((KanSequence.signedLoopTail X.toKanSequence).level n).space)).hom)
    (transpose_curry'_unit _).symm (transpose_curry'_unit _).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum
