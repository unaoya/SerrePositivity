module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitStageSquare
public import SerrePositivity.KST.Spectra.RawSpectrumParameterHomFamilies

/-!
概要：単位側の段区間の終点を、同じ全 Hom の単位後合成から得る厳密な列射へ表示する。
方針：元のパラメータ族と cotensor 値の列射の往復を転置で計算する。
規約：同じ実区間の端点表示だけを変える。使われ方：厳密な二つの終点の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 同じ単位と射影を後合成した、元の全 Hom のパラメータ族。 -/
def kanAdjointTracedUnitFamily :
    A ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  φ ≫ pointedPost X (OmegaSpectrum.sequenceHom (OmegaSpectrum.tracedSignedLoopUnit Y)) ≫
    pointedPost X (OmegaSpectrum.signedLoopProjection Y)

/-- 全 Hom の単位後合成そのものに対応する、厳密な cotensor 値の列射。 -/
def kanAdjointTracedUnitParameterHom :
    KanSequence.Hom X.toKanSequence
      (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)) :=
  homOfParameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
    (kanAdjointTracedUnitFamily X Y φ)

/-- 同じ厳密な列射の段は、元の単位後合成の段評価の転置。 -/
lemma kanAdjointTracedUnitParameterHom_app (n : ℕ) :
    (kanAdjointTracedUnitParameterHom X Y φ).app n =
      PointedMapping.transpose (kanAdjointTracedUnitFamily X Y φ ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) := by
  have h := congrArg PointedMapping.transpose
    (homOfParameterFamily_transpose_evaluation X
      (KanSequence.signedLoopTail Y.toKanSequence) A (kanAdjointTracedUnitFamily X Y φ) n)
  rw [PointedMapping.transpose_transpose] at h
  exact h

/-- 元の Kan 随伴の段から、同じ厳密な単位後合成の列射への実区間。 -/
def kanAdjointTracedUnitStageInterval (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level n).space)
      (kanAdjointParameterStage X Y φ n) ((kanAdjointTracedUnitParameterHom X Y φ).app n) := by
  refine (kanAdjointTracedUnitEvaluationInterval X Y φ n).basedTranspose.changeEndpoints rfl ?_
  simpa only [kanAdjointTracedUnitFamily, Category.assoc] using
    kanAdjointTracedUnitParameterHom_app X Y φ n

/-- 厳密な終点の表示へ移しても、同じ転置された実区間そのものを保持。 -/
lemma kanAdjointTracedUnitStageInterval_path (n : ℕ) :
    (kanAdjointTracedUnitStageInterval X Y φ n).path =
      (kanAdjointTracedUnitEvaluationInterval X Y φ n).basedTranspose.path := rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
