module

public import SerrePositivity.KST.Spectra.SequenceTracedRectificationTriangles
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStructureIntervals

/-!
概要：元の普遍係数区間から、比較区間と実構造三角形を全段に保持する Kan 随伴比較を作る。
方針：同じ構造区間を転置し、区間を保持する列の厳密化へ入力して全パラメータ族へ戻す。
規約：高次整合性を仮定しない。使われ方：非零境界の実際の比較区間の選択。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 元の普遍係数区間の同じ転置を、実際の列の構造比較へ移す。 -/
def kanAdjointTracedStructureInterval (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level
        (n + 1)).space)
      (X.sigma n ≫ kanAdjointParameterStage X Y φ (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ kanAdjointParameterStage X Y φ n ≫
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) := by
  let P := (kanAdjointParameterStructureInterval X Y φ n).basedTranspose
  have hr := transpose_restriction X (KanSequence.signedLoopTail Y.toKanSequence) A n
    (φ ≫ kanAdjointParameterLeft X Y (n + 1))
  have hl := transpose_step X (KanSequence.signedLoopTail Y.toKanSequence) A n
    (φ ≫ kanAdjointParameterLeft X Y n)
  exact P.changeEndpoints hr.symm hl.symm

/-- 比較区間を全段に保持して厳密化した、実際の cotensor 値の列射。 -/
def kanAdjointTracedParameterHom :
    KanSequence.Hom X.toKanSequence
      (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)) :=
  KanSequence.tracedRectify X.sigma_mono (kanAdjointParameterStage X Y φ)
    (kanAdjointTracedStructureInterval X Y φ)

/-- 構造三角形を保持する帰納構成から得た、元の全パラメータの Kan 随伴比較。 -/
def kanAdjointTracedComparison :
    A ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  parameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
    (kanAdjointTracedParameterHom X Y φ)

/-- 元の段座標から修正後の段座標への、保存した同じ比較区間を回収する。 -/
def kanAdjointTracedEvaluationInterval (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
      (φ ≫ kanAdjointParameterLeft X Y n)
      (kanAdjointTracedComparison X Y φ ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) := by
  let Q := KanSequence.tracedRectifyComparison (X := X.toKanSequence)
    (Y := KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))
    X.sigma_mono (kanAdjointParameterStage X Y φ) (kanAdjointTracedStructureInterval X Y φ) n
  let P := PointedMapping.VerticalPath.basedTranspose (A := (X.level n).space) (U := A)
    (V := ((KanSequence.signedLoopTail Y.toKanSequence).level n).space) Q
  exact P.changeEndpoints (PointedMapping.transpose_transpose
    (φ ≫ kanAdjointParameterLeft X Y n)).symm
    (parameterFamily_evaluation X (KanSequence.signedLoopTail Y.toKanSequence) A
      (kanAdjointTracedParameterHom X Y φ) n)

/-- 零段の元の Kan 随伴座標は、全列の厳密化後も厳密に保持する。 -/
lemma kanAdjointTracedComparison_zero :
    kanAdjointTracedComparison X Y φ ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) 0 =
        φ ≫ kanAdjointParameterLeft X Y 0 := by
  have h := parameterFamily_evaluation X (KanSequence.signedLoopTail Y.toKanSequence) A
    (kanAdjointTracedParameterHom X Y φ) 0
  change _ = PointedMapping.transpose (kanAdjointParameterStage X Y φ 0) at h
  rw [kanAdjointParameterStage, PointedMapping.transpose_transpose] at h
  exact h

/-- 元の構造区間・前段比較・次段比較の制限を持つ、帰納段の同じ実三角形。 -/
def kanAdjointTracedStructureTriangle (n : ℕ) :
    SSet.Edge.CompStruct (kanAdjointTracedStructureInterval X Y φ n).edge
      (KanSequence.tracedRectificationStepPath (X := X.toKanSequence)
        (Y := KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))
        (kanAdjointParameterStage X Y φ) n
        (KanSequence.tracedRectificationStage (X := X.toKanSequence)
          (Y := KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))
          X.sigma_mono (kanAdjointParameterStage X Y φ)
          (kanAdjointTracedStructureInterval X Y φ) n)).edge
      (KanSequence.tracedRectifyRestrictionPath (X := X.toKanSequence)
        (Y := KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))
        X.sigma_mono (kanAdjointParameterStage X Y φ)
        (kanAdjointTracedStructureInterval X Y φ) n).edge :=
  KanSequence.tracedRectifyComparison_triangle (X := X.toKanSequence)
    (Y := KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))
    X.sigma_mono (kanAdjointParameterStage X Y φ) (kanAdjointTracedStructureInterval X Y φ) n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
