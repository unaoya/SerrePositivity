module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParametricInput
public import SerrePositivity.KST.Spectra.SpectrumParametricAdjointSquare
public import SerrePositivity.KST.Spectra.SignedAdjointParametricReverseNaturality
public import SerrePositivity.KST.Spectra.SignedLoopTracedStructureInterval

/-!
概要：元の全 Hom の実入力から、単位に使う同じ逆向き符号比較の全族自然性を構成する。
方針：保存済み自然性から構成した入力と、実証した厳密全族 Ω 可換式を四三角形比較へ渡す。
規約：全族自然性や実入力の存在を仮定しない。使われ方：元の単位構造の主正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元の全 Hom で具体化した、三つの実正方形と保存済み四三角形を保持する比較データ。 -/
def kanAdjointSignedReverseParametricComparison (X Y : OmegaSpectrum.{u}) (n : ℕ) :=
  SignedAdjointPaths.reverseParametricNaturalityComparison
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma (n + 2))) (X.toKanSequence_omega (n + 2))
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (Y.sigma (n + 2))) (Y.toKanSequence_omega (n + 2))
    (pointedEvaluation X Y.toKanSequence (n + 2))
    (pointedEvaluation X Y.toKanSequence (n + 3))
    (pointedEvaluation_parametric_adjoint X Y (n + 2))
    (KanSequence.kanAdjoint X.toKanSequence n)
    (KanSequence.kanAdjoint X.toKanSequence (n + 1))
    (KanSequence.kanAdjoint Y.toKanSequence n)
    (KanSequence.kanAdjoint Y.toKanSequence (n + 1))
    (PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n))
    (kanAdjointParametricInputComparison X Y n)

/-- 単位構造に使う元の同じ逆向き符号比較区間の、無条件の全族自然性正方形。 -/
def kanAdjointSignedReverseParametricSquare (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    SSet.Homotopy
      ((PointedMapping.VerticalPath.basedPost
        (KanSequence.signedLoopStructureReverse X.toKanSequence X.toKanSequence_omega n).path
        (SignedAdjointPaths.targetParametricPost
          (pointedEvaluation X Y.toKanSequence (n + 2)))).path)
      (((PointedMapping.VerticalPath.basedIhomMap (pointedSpace X Y.toKanSequence)
        (KanSequence.signedLoopStructureReverse Y.toKanSequence Y.toKanSequence_omega n).path).pre
          (PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n))).path) :=
  SignedAdjointPaths.reverseParametricNaturalitySquare
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma (n + 2))) (X.toKanSequence_omega (n + 2))
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (Y.sigma (n + 2))) (Y.toKanSequence_omega (n + 2))
    (pointedEvaluation X Y.toKanSequence (n + 2))
    (pointedEvaluation X Y.toKanSequence (n + 3))
    (pointedEvaluation_parametric_adjoint X Y (n + 2))
    (KanSequence.kanAdjoint X.toKanSequence n)
    (KanSequence.kanAdjoint X.toKanSequence (n + 1))
    (KanSequence.kanAdjoint Y.toKanSequence n)
    (KanSequence.kanAdjoint Y.toKanSequence (n + 1))
    (PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n))
    (kanAdjointParametricInputComparison X Y n)

/-- 二次元射は、同じ実入力・四三角形比較から回収した射そのもの。 -/
lemma kanAdjointSignedReverseParametricSquare_h (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (kanAdjointSignedReverseParametricSquare X Y n).h =
      (SquareAdjustment.TrianglePairComparison.square _ _ _ _ _ _ _
        (kanAdjointSignedReverseParametricComparison X Y n)).h := rfl

/-- 同じ実入力の第二辺の正方形を、元の全 Hom へ具体化したもの。 -/
def kanAdjointSignedSecondParametricSquare (X Y : OmegaSpectrum.{u}) (n : ℕ) :=
  SignedAdjointPaths.secondPathParametricNaturalitySquare
    (KanSequence.kanAdjoint X.toKanSequence n)
    (KanSequence.kanAdjoint X.toKanSequence (n + 1))
    (KanSequence.kanAdjoint Y.toKanSequence n)
    (KanSequence.kanAdjoint Y.toKanSequence (n + 1))
    (PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n))
    (pointedEvaluation X Y.toKanSequence (n + 2)) (kanAdjointParametricInputComparison X Y n)

/-- 同じ実入力の定数辺の正方形も、元の全 Hom へ具体化する。 -/
def kanAdjointSignedConstantParametricSquare (X Y : OmegaSpectrum.{u}) (n : ℕ) :=
  SignedAdjointPaths.constantPathParametricNaturalitySquare
    (KanSequence.kanAdjoint X.toKanSequence n)
    (KanSequence.kanAdjoint X.toKanSequence (n + 1))
    (KanSequence.kanAdjoint Y.toKanSequence n)
    (KanSequence.kanAdjoint Y.toKanSequence (n + 1))
    (PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n))
    (pointedEvaluation X Y.toKanSequence (n + 2)) (kanAdjointParametricInputComparison X Y n)

/-- 左境界全体は、同じ実入力から作った第二正方形の終境界。 -/
lemma kanAdjointSignedReverseParametricSquare_left (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointSignedReverseParametricSquare X Y n).h =
      SquareAdjustment.rightSide ≫ (kanAdjointSignedSecondParametricSquare X Y n).h :=
  SquareAdjustment.TrianglePairComparison.left _ _ _ _ _ _ _
    (kanAdjointSignedReverseParametricComparison X Y n)

/-- 右境界全体も、同じ実入力から作った第三正方形の終境界。 -/
lemma kanAdjointSignedReverseParametricSquare_right (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointSignedReverseParametricSquare X Y n).h =
      SquareAdjustment.rightSide ≫ (kanAdjointSignedConstantParametricSquare X Y n).h :=
  SquareAdjustment.TrianglePairComparison.right _ _ _ _ _ _ _
    (kanAdjointSignedReverseParametricComparison X Y n)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
