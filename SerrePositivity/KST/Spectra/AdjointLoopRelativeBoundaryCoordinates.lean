module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeFullCompatibleMaps
public import SerrePositivity.KST.Spectra.AdjointLoopRelativeCompatibleMaps
public import SerrePositivity.KST.Spectra.PointedIhomParameterExchange
public import SerrePositivity.KST.Spectra.PointedIhomActionLaws

/-!
概要：元の単位の左右境界を、各段の元の豊穣 Hom の作用へ厳密に戻す。
方針：普遍パラメータ族の転置座標と内部 Hom の全作用を照合する。
規約：右射影を別の代表や π 同型だけへ変更しない。
使われ方：左右境界を保つ組の恒等・合成保存の全段での検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 概要：普遍パラメータ族の左境界は元の相対左因子の後合成そのもの。
方針：全段で転置の標的自然性と普遍族の厳密回収を使う。
規約：元の全 Hom と指定左因子を保持する。
使われ方：左境界を保つ組の合成の照合。 -/
lemma inclusionParameterFamily_universal (X Y : OmegaSpectrum.{u}) :
    inclusionParameterFamily X Y _ (universalParameterHom X Y) = inclusionPost X Y := by
  apply RawSpectrumMapping.pointed_hom_ext X (middle Y).toKanSequence
  intro n
  dsimp only [inclusionParameterFamily]
  rw [RawSpectrumMapping.parameterFamily_evaluation]
  change PointedMapping.transpose
      ((universalParameterHom X Y).app n ≫ (ihom _).map ((inclusion Y).app n)) =
    inclusionPost X Y ≫ RawSpectrumMapping.pointedEvaluation X (middle Y).toKanSequence n
  have h := RawSpectrumMapping.homOfParameterFamily_transpose_evaluation
    X Y.toKanSequence (RawSpectrumMapping.pointedSpace X Y.toKanSequence) (𝟙 _) n
  change PointedMapping.transpose ((universalParameterHom X Y).app n) =
    𝟙 _ ≫ RawSpectrumMapping.pointedEvaluation X Y.toKanSequence n at h
  exact (PointedMapping.transpose_post ((universalParameterHom X Y).app n)
    ((inclusion Y).app n)).trans (by
      rw [h, Category.id_comp]
      exact (RawSpectrumMapping.pointedPost_evaluation X
        (⟨(inclusion Y).app, (inclusion Y).comm⟩ :
          KanSequence.Hom Y.toKanSequence (middle Y).toKanSequence) n).symm)

/-- 概要：普遍族の右境界の各段は元の次段の Hom への loop 作用と右射影の前合成。
方針：内部 Hom の全パラメータ作用の転置式へ普遍族と元の右射影を代入する。
規約：各段の元の q と全 Hom の実評価を保持する。
使われ方：右境界を保つ組の豊穣合成の照合。 -/
lemma projectionParameterFamily_universal_evaluation (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    projectionParameterFamily X Y _ (universalParameterHom X Y) ≫
      RawSpectrumMapping.pointedEvaluation (middle X) (target Y) n =
    RawSpectrumMapping.pointedEvaluation X Y.toKanSequence (n + 1) ≫
      PointedMapping.ihomAction PointedSimplicialSet.circle.{u}
        (X.level (n + 1)).space (Y.level (n + 1)).space ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((projection X).app n) ((target Y).level n).space := by
  dsimp only [projectionParameterFamily]
  rw [RawSpectrumMapping.parameterFamily_evaluation]
  change PointedMapping.transpose
      ((projection X).app n ≫
        (ihom PointedSimplicialSet.circle.{u}).map ((universalParameterHom X Y).app (n + 1)) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u}
            (RawSpectrumMapping.pointedSpace X Y.toKanSequence)
            (Y.level (n + 1)).space).hom) = _
  have h := PointedMapping.transpose_ihomParameterAction
    (PointedMapping.transpose ((universalParameterHom X Y).app (n + 1))) ((projection X).app n)
  rw [PointedMapping.transpose_transpose] at h
  have hu := RawSpectrumMapping.homOfParameterFamily_transpose_evaluation
    X Y.toKanSequence (RawSpectrumMapping.pointedSpace X Y.toKanSequence) (𝟙 _) (n + 1)
  change PointedMapping.transpose ((universalParameterHom X Y).app (n + 1)) =
    𝟙 _ ≫ RawSpectrumMapping.pointedEvaluation X Y.toKanSequence (n + 1) at hu
  exact h.trans (by
    rw [hu, Category.id_comp]
    rfl)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
