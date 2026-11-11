module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterStructure
public import SerrePositivity.KST.Spectra.SequenceParameterTranspose
public import SerrePositivity.KST.Spectra.SequenceParameterRectification

/-!
概要：元の全 Hom をパラメータとする Kan 随伴の族を、符号付き loop 列への厳密な族にする。
方針：全パラメータの構造成分式を転置し、既存の列の厳密化へ入力する。
規約：絶対厳密化。使われ方：loop 比較の段座標と普遍評価の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 転置した元の Kan 随伴の全パラメータ族は、cotensor 列の構造成分式を満たす。 -/
lemma kanAdjointParameter_transpose_condition (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.componentOf
      (PointedSimplicialSet.circle.{u} ◁
        PointedMapping.transpose (kanAdjointParameterLeft X Y n) ≫
        (KanSequence.mapping (pointedSpace X Y.toKanSequence)
          (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) =
    PointedMapping.componentOf (X.sigma n ≫
      PointedMapping.transpose (kanAdjointParameterLeft X Y (n + 1))) := by
  have h := PointedMapping.componentOf_transpose (kanAdjointParameterLeft_condition X Y n)
  have hl := transpose_step X (KanSequence.signedLoopTail Y.toKanSequence)
    (pointedSpace X Y.toKanSequence) n (kanAdjointParameterLeft X Y n)
  have hr := transpose_restriction X (KanSequence.signedLoopTail Y.toKanSequence)
    (pointedSpace X Y.toKanSequence) n (kanAdjointParameterLeft X Y (n + 1))
  exact (congrArg PointedMapping.componentOf hl.symm).trans
    (h.trans (congrArg PointedMapping.componentOf hr))

/-- 元の全 Hom パラメータ上で厳密化した、符号付き loop 列への比較。 -/
def kanAdjointParameterRectification (X Y : OmegaSpectrum.{u}) :
    pointedSpace X Y.toKanSequence ⟶
      pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  rectifyParameter X (KanSequence.signedLoopTail Y.toKanSequence)
    (pointedSpace X Y.toKanSequence)
    (fun n ↦ PointedMapping.transpose (kanAdjointParameterLeft X Y n))
    (kanAdjointParameter_transpose_condition X Y)

/-- 厳密化後の段評価は、元の全 Hom 上の Kan 随伴への後合成と同じ成分。 -/
lemma kanAdjointParameterRectification_evaluation_component
    (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.componentOf (kanAdjointParameterRectification X Y ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) =
      PointedMapping.componentOf (kanAdjointParameterLeft X Y n) := by
  have h := rectifyParameter_evaluation_component X
    (KanSequence.signedLoopTail Y.toKanSequence) (pointedSpace X Y.toKanSequence)
    (fun n ↦ PointedMapping.transpose (kanAdjointParameterLeft X Y n))
    (kanAdjointParameter_transpose_condition X Y) n
  rw [PointedMapping.transpose_transpose] at h
  exact h

/-- 元の全 Hom の基点を固定する、厳密化した段評価と元の Kan 随伴の実際のホモトピー。 -/
lemma kanAdjointParameterRectification_evaluation_homotopy
    (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    ∃ H : SSet.Homotopy (kanAdjointParameterRectification X Y ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n).right
        (kanAdjointParameterLeft X Y n).right,
      (pointedSpace X Y.toKanSequence).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          (kanAdjointParameterTarget X Y n).hom := by
  let parameterTargetKan : KanComplex (kanAdjointParameterTarget X Y n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact (PointedMapping.piZero_eq_iff_pointedHomotopy _ _).1
    (kanAdjointParameterRectification_evaluation_component X Y n)

/-- 元の全パラメータの零段の Kan 随伴への後合成は、厳密化でもそのまま保持する。 -/
lemma kanAdjointParameterRectification_evaluation_zero (X Y : OmegaSpectrum.{u}) :
    kanAdjointParameterRectification X Y ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) 0 =
      kanAdjointParameterLeft X Y 0 := by
  exact (rectifyParameter_evaluation_zero X (KanSequence.signedLoopTail Y.toKanSequence)
    (pointedSpace X Y.toKanSequence)
    (fun n ↦ PointedMapping.transpose (kanAdjointParameterLeft X Y n))
    (kanAdjointParameter_transpose_condition X Y)).trans
      (PointedMapping.transpose_transpose _)

/-- 通常の円への射影後も、元の全 Hom の随伴座標と同じ成分を持つ。 -/
lemma kanAdjointParameterRectification_restriction_component
    (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.componentOf ((kanAdjointParameterRectification X Y ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) ≫
      kanAdjointParameterRestriction X Y n) =
    PointedMapping.componentOf (pointedEvaluation X Y.toKanSequence n ≫
      PointedObject.basedHomMap (X.level n).space
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space (Y.sigma n))) := by
  have h := PointedMapping.componentOf_comp_right
    (kanAdjointParameterRectification_evaluation_component X Y n)
    (kanAdjointParameterRestriction X Y n)
  rw [kanAdjointParameterLeft_restriction] at h
  exact h

/-- 零段の通常の円への射影は、元の全パラメータの随伴座標に厳密に一致する。 -/
lemma kanAdjointParameterRectification_restriction_zero (X Y : OmegaSpectrum.{u}) :
    (kanAdjointParameterRectification X Y ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) 0) ≫
      kanAdjointParameterRestriction X Y 0 =
    pointedEvaluation X Y.toKanSequence 0 ≫
      PointedObject.basedHomMap (X.level 0).space
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level 0).space (Y.level (0 + 1)).space (Y.sigma 0)) := by
  rw [kanAdjointParameterRectification_evaluation_zero, kanAdjointParameterLeft_restriction]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
