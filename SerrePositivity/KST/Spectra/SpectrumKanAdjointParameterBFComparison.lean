module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterRectification
public import SerrePositivity.KST.Spectra.RawSpectrumPointedPostLifting
public import SerrePositivity.KST.Spectra.SignedLoopModel

/-!
概要：元の全 Hom 上の符号付き loop 比較を、同じ BF 模型の全 Hom へ持ち上げる。
方針：BF 射影の後合成の全単射 RLP を適用し、全体と各段の厳密な射影式を計算する。
規約：持ち上げの自然性は仮定しない。使われ方：元の普遍評価と BF 比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元の符号付き loop の BF 射影は、各段で全ての単射に RLP を持つ。 -/
lemma signedLoopProjection_level_rlp (Y : OmegaSpectrum.{u}) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((OmegaSpectrum.signedLoopProjection Y).app n).right :=
  (KanSequence.replacementStage (KanSequence.signedLoopTail Y.toKanSequence) n).projection_rlp

/-- 元の全 Hom パラメータを持つ、符号付き loop の BF 模型への実際の全 Hom 比較。 -/
def kanAdjointParameterBFComparison (X Y : OmegaSpectrum.{u}) :
    pointedSpace X Y.toKanSequence ⟶
      pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence :=
  pointedPostLift X (OmegaSpectrum.signedLoopProjection Y)
    (signedLoopProjection_level_rlp Y) (kanAdjointParameterRectification X Y)

/-- BF 比較を元の loop 列へ射影すると、元の全 Hom 上の厳密化した族そのものになる。 -/
@[reassoc]
lemma kanAdjointParameterBFComparison_projection (X Y : OmegaSpectrum.{u}) :
    kanAdjointParameterBFComparison X Y ≫
      pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
      kanAdjointParameterRectification X Y :=
  pointedPostLift_fac X (OmegaSpectrum.signedLoopProjection Y)
    (signedLoopProjection_level_rlp Y) (kanAdjointParameterRectification X Y)

/-- 各段の BF 射影座標は、同じ全パラメータの元の厳密化座標。 -/
lemma kanAdjointParameterBFComparison_projected_evaluation
    (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (kanAdjointParameterBFComparison X Y ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
      PointedObject.basedHomMap (X.level n).space
        ((OmegaSpectrum.signedLoopProjection Y).app n) =
    kanAdjointParameterRectification X Y ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n := by
  rw [Category.assoc, ← pointedPost_evaluation, ← Category.assoc,
    kanAdjointParameterBFComparison_projection]

/-- BF 射影後の段座標は、元の全 Hom の評価を Kan 随伴へ後合成した族と同じ成分。 -/
lemma kanAdjointParameterBFComparison_projected_component
    (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.componentOf ((kanAdjointParameterBFComparison X Y ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
      PointedObject.basedHomMap (X.level n).space
        ((OmegaSpectrum.signedLoopProjection Y).app n)) =
      PointedMapping.componentOf (kanAdjointParameterLeft X Y n) := by
  rw [kanAdjointParameterBFComparison_projected_evaluation]
  exact kanAdjointParameterRectification_evaluation_component X Y n

/-- 零段では、BF 射影後の元の普遍評価と Kan 随伴への後合成が厳密に一致する。 -/
lemma kanAdjointParameterBFComparison_projected_zero (X Y : OmegaSpectrum.{u}) :
    (kanAdjointParameterBFComparison X Y ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence 0) ≫
      PointedObject.basedHomMap (X.level 0).space
        ((OmegaSpectrum.signedLoopProjection Y).app 0) = kanAdjointParameterLeft X Y 0 := by
  rw [kanAdjointParameterBFComparison_projected_evaluation]
  exact kanAdjointParameterRectification_evaluation_zero X Y

end SerrePositivity.KST.Spectra.RawSpectrumMapping
