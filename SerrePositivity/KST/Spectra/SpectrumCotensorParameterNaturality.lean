module

public import SerrePositivity.KST.Spectra.SpectrumEvaluationPostCoordinates
public import SerrePositivity.KST.Spectra.CotensorRestriction
public import SerrePositivity.KST.Spectra.PointedRelativeTransposePaths
public import SerrePositivity.KST.Spectra.RawSpectrumPointedPreComposition

/-!
概要：元の BF cotensor の普遍評価と evaluationPost の、源パラメータについての厳密な自然性。
方針：cotensorPre の同じ比較式を転置し、全整合写像の評価と smash 合成へ移す。
規約：cotensorPre の関手法則や自然性を新たに仮定しない。
使われ方：通常円と Kan 円の比較、元の全 Hom の evaluationPost を保つ移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra

/-- 二つの厳密な可換正方形を curry すると、源パラメータの制限と後合成が可換となる。 -/
lemma curry_parameter_square {A B R P Q E F : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (eA : A ⟶ P) (eB : B ⟶ Q) (s : P ⟶ Q)
    (cA : P ⊗ R ⟶ E) (cB : Q ⊗ R ⟶ F) (p : E ⟶ F)
    (hc : cA ≫ p = s ▷ R ≫ cB) (he : eA ≫ s = i ≫ eB) :
    curry (eA ▷ R ≫ cA) ≫ (ihom A).map p =
      curry (eB ▷ R ≫ cB) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i F := by
  apply uncurry_injective
  rw [uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, uncurry_pre_app]
  simp only [uncurry_curry]
  rw [Category.assoc, hc, ← comp_whiskerRight_assoc, he, comp_whiskerRight, Category.assoc]

namespace OmegaSpectrum
variable {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)

/-- BF cotensor の元の段評価は、同じ源パラメータの制限と厳密に可換。 -/
lemma cotensorEvaluationAt_parameter (X : OmegaSpectrum.{u}) (n : ℕ) :
    CotensorCompatible.evaluationAt A X n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((cotensorPre i X).app n) (X.level n).space =
    i ≫ CotensorCompatible.evaluationAt B X n := by
  have h := congrArg PointedMapping.transpose (cotensorPre_comparison i X n)
  have hl := PointedMapping.transpose_pre_outer ((cotensorProjection A X).app n)
    ((cotensorPre i X).app n)
  have hr := PointedMapping.transpose_pre_inner ((cotensorProjection B X).app n) i
  exact hl.symm.trans (h.trans hr)

/-- 元の普遍評価全体も、BF 制限射による前合成と厳密に可換。 -/
lemma cotensorEvaluation_parameter (X : OmegaSpectrum.{u}) :
    cotensorEvaluation A X ≫
      RawSpectrumMapping.pointedPre (cotensorPre i X) X.toKanSequence =
    i ≫ cotensorEvaluation B X := by
  apply RawSpectrumMapping.pointed_hom_ext (cotensor B X) X.toKanSequence
  intro n
  rw [Category.assoc, RawSpectrumMapping.pointedPre_evaluation, ← Category.assoc,
    cotensorEvaluation_evaluation, Category.assoc, cotensorEvaluation_evaluation]
  exact cotensorEvaluationAt_parameter i X n

namespace CotensorCompatible

/-- 元の evaluationPost 全体の源パラメータ自然性。両辺は同じ全 Hom の実際の射。 -/
lemma evaluationPost_parameter (X Y : OmegaSpectrum.{u}) :
    evaluationPost A X Y ≫ (ihom A).map
      (RawSpectrumMapping.pointedPre (cotensorPre i X) Y.toKanSequence) =
    evaluationPost B X Y ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i
      (RawSpectrumMapping.pointedSpace (cotensor B X) Y.toKanSequence) := by
  exact curry_parameter_square i (cotensorEvaluation A X) (cotensorEvaluation B X)
    (RawSpectrumMapping.pointedPre (cotensorPre i X) X.toKanSequence)
    (RawSpectrumMapping.pointedComposition (cotensor A X) X Y.toKanSequence)
    (RawSpectrumMapping.pointedComposition (cotensor B X) X Y.toKanSequence)
    (RawSpectrumMapping.pointedPre (cotensorPre i X) Y.toKanSequence)
    (RawSpectrumMapping.pointedComposition_pre (cotensorPre i X) X Y.toKanSequence)
    (cotensorEvaluation_parameter i X)

end CotensorCompatible
end OmegaSpectrum
end SerrePositivity.KST.Spectra
