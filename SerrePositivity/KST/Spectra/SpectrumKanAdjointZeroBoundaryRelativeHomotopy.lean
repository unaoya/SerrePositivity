module

public import SerrePositivity.KST.Spectra.SequenceParameterRelativeHomotopy
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointZeroBoundaryBFComparison

/-!
概要：元の零境界 Kan 随伴比較の各段を、指定部分全体で零に固定するホモトピーで照合する。
方針：保持した垂直修正鎖の圧縮・転置を実際の比較へ適用し、BF 射影の厳密式で移送する。
規約：全列のホモトピーではない。使われ方：零境界パラメータ族の相対ホモトピー類の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right] (hzero : j ≫ φ = 0)

/-- 元の各段との比較は、基点と指定部分全体を全区間で零に固定する。 -/
lemma kanAdjointZeroBoundaryComparison_evaluation_relative_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy (kanAdjointZeroBoundaryComparison X Y φ j hzero ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n).right
        (φ ≫ kanAdjointParameterLeft X Y n).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (B.right ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom := by
  have h := rectifyParameterRelative_evaluation_relative_homotopy X
    (KanSequence.signedLoopTail Y.toKanSequence) j 0 (kanAdjointParameterStage X Y φ)
    (kanAdjointZeroBoundaryProjectionCondition X Y φ j hzero)
    (kanAdjointZeroBoundaryStructureCondition X Y φ j hzero) n
  rw [kanAdjointParameterStage, PointedMapping.transpose_transpose] at h
  obtain ⟨H, hbase, hrel⟩ := h
  rw [zero_comp, PointedObject.zero_right, comp_toUnit_assoc] at hrel
  exact ⟨H, hbase, hrel⟩

/-- BF 射影後の元の座標比較でも、指定部分全体と基点を全区間で零に固定する。 -/
lemma kanAdjointZeroBoundaryBFComparison_projected_relative_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy ((kanAdjointZeroBoundaryBFComparison X Y φ j hzero ≫
        pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
        PointedObject.basedHomMap (X.level n).space
          ((OmegaSpectrum.signedLoopProjection Y).app n)).right
        (φ ≫ kanAdjointParameterLeft X Y n).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (B.right ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom := by
  rw [kanAdjointZeroBoundaryBFComparison_projected_evaluation]
  exact kanAdjointZeroBoundaryComparison_evaluation_relative_homotopy X Y φ j hzero n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
