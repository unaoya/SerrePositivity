module

public import SerrePositivity.KST.Spectra.SpectrumTracedSourceEvaluationDifference
public import SerrePositivity.KST.Spectra.PointedParametricEvaluationTranspose

/-!
概要：保存済みの全 Hom Kan 随伴自然性の両端を、全族作用の転置座標へ厳密同定する。
方針：同じ段評価と随伴を用い、転置の後合成公式とパラメータ評価公式を使う。
規約：元の自然性区間を選び直さない。使われ方：符号付き随伴比較への実入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元の左座標の転置は、転置した段評価から標的の同じ Kan 随伴への全族後合成。 -/
lemma kanAdjointParameterLeft_transpose (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.transpose (kanAdjointParameterLeft X Y n) =
      PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n) ≫
        PointedObject.basedHomMap (pointedSpace X Y.toKanSequence)
          (KanSequence.kanAdjoint Y.toKanSequence n) :=
  PointedMapping.transpose_post (pointedEvaluation X Y.toKanSequence n)
    (KanSequence.kanAdjoint Y.toKanSequence n)

/-- 元の右座標の転置は、源の同じ Kan 随伴への一段先の段評価の標準全族作用。 -/
lemma kanAdjointParameterRight_transpose (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.transpose (kanAdjointParameterRight X Y n) =
      KanSequence.kanAdjoint X.toKanSequence n ≫
        PointedMapping.parametricPost CirclePower.space.{u}
          (pointedEvaluation X Y.toKanSequence (n + 1)) := by
  have he := PointedMapping.transpose_pre_parametricPost
    (KanSequence.kanAdjoint X.toKanSequence n) (pointedEvaluation X Y.toKanSequence (n + 1))
  change PointedMapping.transpose
    (KanSequence.kanAdjoint X.toKanSequence n ≫
      PointedMapping.parametricPost CirclePower.space.{u}
        (pointedEvaluation X Y.toKanSequence (n + 1))) = kanAdjointParameterRight X Y n at he
  exact (congrArg PointedMapping.transpose he).symm.trans
    (PointedMapping.transpose_transpose _)

/-- 保存済みの実自然性区間の同じ転置。両端を全族入力座標で表示する。 -/
def kanAdjointParametricNaturalityInterval (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom (pointedSpace X Y.toKanSequence)
        (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space)))
      (PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n) ≫
        PointedObject.basedHomMap (pointedSpace X Y.toKanSequence)
          (KanSequence.kanAdjoint Y.toKanSequence n))
      (KanSequence.kanAdjoint X.toKanSequence n ≫
        PointedMapping.parametricPost CirclePower.space.{u}
          (pointedEvaluation X Y.toKanSequence (n + 1))) :=
  (OmegaSpectrum.CotensorCompatible.kanAdjointSourceNaturalityInterval X Y n).basedTranspose
    |>.changeEndpoints (kanAdjointParameterLeft_transpose X Y n).symm
      (kanAdjointParameterRight_transpose X Y n).symm

/-- 全族入力に使う実辺は、保存済みの元の自然性区間の同じ転置を保持する。 -/
lemma kanAdjointParametricNaturalityInterval_path (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (kanAdjointParametricNaturalityInterval X Y n).path =
      (PointedMapping.VerticalPath.basedTranspose
        (OmegaSpectrum.CotensorCompatible.kanAdjointSourceNaturalityInterval X Y n)).path := rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
