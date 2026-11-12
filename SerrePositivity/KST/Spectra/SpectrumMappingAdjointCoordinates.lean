module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPointed
public import SerrePositivity.KST.Spectra.SpectrumMappingStepEquivalence

/-!
概要：元のスペクトルの全 Hom の構造条件を、各段の随伴構造射で表示する。
方針：pointedStep と curry の厳密な式を、元の段評価の条件に合成する。
規約：元の全 Hom パラメータを保持。使われ方：Kan 円への随伴の自然性の全パラメータ化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 点つき段の比較を curry すると、元の標的の随伴構造射への後合成。 -/
lemma pointedStep_curry (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    pointedStep X Y.toKanSequence n ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle (X.level n).space
          (Y.level (n + 1)).space).hom =
      PointedObject.basedHomMap (X.level n).space
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space (Y.sigma n)) :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom_adjoint PointedSimplicialSet.circle
    (X.level n).space (Y.level n).space (Y.level (n + 1)).space (Y.sigma n)

/-- 全 Hom の隣接二段の評価の条件は、元の随伴への後合成に厳密一致する。 -/
lemma pointedEvaluation_adjoint_condition (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    pointedEvaluation X Y.toKanSequence (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle (X.level n).space
        (Y.level (n + 1)).space).hom =
    pointedEvaluation X Y.toKanSequence n ≫ PointedObject.basedHomMap (X.level n).space
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space (Y.sigma n)) := by
  have h := congrArg (fun f ↦ f ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle (X.level n).space
      (Y.level (n + 1)).space).hom) (pointedEvaluation_condition X Y.toKanSequence n)
  simp only [Category.assoc] at h
  exact h.trans (congrArg (pointedEvaluation X Y.toKanSequence n ≫ ·)
    (pointedStep_curry X Y n))

end SerrePositivity.KST.Spectra.RawSpectrumMapping
