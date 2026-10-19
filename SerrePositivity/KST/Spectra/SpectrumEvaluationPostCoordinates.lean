module

public import SerrePositivity.KST.Spectra.SpectrumCotensorCompatibleMaps

/-!
概要：元の普遍評価の後合成を、各段の全 Hom パラメータの curry で厳密表示する。
方針：整合写像の合成と普遍評価の段評価の式を使う。
規約：元の evaluationPost を保持。使われ方：円の全写像空間比較と構造射の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible

/-- 元の普遍評価の各段の点つき射。元の BF 置換射影を二変数で評価したもの。 -/
def evaluationAt (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u}) (n : ℕ) :
    A ⟶ PointedObject.basedHom ((cotensor A X).level n).space (X.level n).space :=
  curry ((β_ ((cotensor A X).level n).space A).hom ≫
    uncurry ((cotensorProjection A X).app n))

/-- 各段の元の評価との後合成を、全ての Hom パラメータについて curry する。 -/
def evaluationPostAt (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedObject.basedHom (X.level n).space (Y.level n).space ⟶
      (ihom A).obj (PointedObject.basedHom ((cotensor A X).level n).space (Y.level n).space) :=
  curry (evaluationAt A X n ▷ PointedObject.basedHom (X.level n).space (Y.level n).space ≫
    MonoidalClosed.comp ((cotensor A X).level n).space (X.level n).space (Y.level n).space)

/-- 元の evaluationPost の段座標は、同じ段の評価の後合成そのもの。 -/
lemma evaluationPost_evaluation (A : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    evaluationPost A X Y ≫ (ihom A).map
        (RawSpectrumMapping.pointedEvaluation (cotensor A X) Y.toKanSequence n) =
      RawSpectrumMapping.pointedEvaluation X Y.toKanSequence n ≫ evaluationPostAt A X Y n := by
  unfold evaluationPost evaluationPostAt
  rw [← curry_natural_right, Category.assoc,
    RawSpectrumMapping.pointedComposition_evaluation]
  dsimp only [RawSpectrumMapping.pointedCompositionFamily]
  rw [← Category.assoc, whiskerRight_comp_tensorHom, cotensorEvaluation_evaluation]
  rw [← curry_natural_left]
  simp only [← Category.assoc]
  exact congrArg (fun t ↦ curry (t ≫ MonoidalClosed.comp
    ((cotensor A X).level n).space (X.level n).space (Y.level n).space))
    (tensorHom_def' (evaluationAt A X n) (RawSpectrumMapping.pointedEvaluation X Y.toKanSequence n))

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
