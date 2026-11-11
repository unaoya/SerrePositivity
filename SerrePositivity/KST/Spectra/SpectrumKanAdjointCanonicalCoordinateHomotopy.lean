module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCanonicalBFComparison
public import SerrePositivity.KST.Spectra.SequenceParameterForwardInterval
public import SerrePositivity.KST.Spectra.PointedRestrictionPathComposition

/-!
概要：元の Kan 随伴座標から最終全列比較への実ホモトピーを、指定した非零境界区間を保って作る。
方針：段調整区間と垂直修正区間を、制限 fibration 上の指定退化三角形へ持ち上げて合成する。
規約：段ごとのホモトピーであり全列のホモトピーではない。使われ方：相対比較の高次整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 調整済み段座標から最終座標への、具体的な非零境界を固定する修正区間。 -/
def kanAdjointCanonicalCorrectionInterval (n : ℕ) :
    { P : PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
        (kanAdjointTracedBoundaryCoordinate X Y φ j n).coordinate
        (kanAdjointCanonicalRelativeComparison X Y φ j ≫
          pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) //
      P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (kanAdjointParameterTarget X Y n)).right =
        SSet.const (PointedMapping.familyVertex (kanAdjointTracedBoundary X Y φ j ≫
          pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n)) } := by
  let f := fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage
  let hb := fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection
  let hf := kanAdjointBoundaryStructure_chain X Y φ j (kanAdjointTracedBoundary X Y φ j)
    (kanAdjointTracedBoundaryHomotopy X Y φ j) (kanAdjointTracedBoundaryCoordinate X Y φ j)
    (kanAdjointCanonicalStageStructurePath X Y φ j)
    (kanAdjointCanonicalStructureContraction X Y φ j)
  let Q := relativeParameterForwardInterval X (KanSequence.signedLoopTail Y.toKanSequence) j
    (kanAdjointTracedBoundary X Y φ j) f hb hf n
  let R := Q.val.changeEndpoints (PointedMapping.transpose_transpose
    (kanAdjointTracedBoundaryCoordinate X Y φ j n).coordinate).symm rfl
  exact ⟨R, Q.property⟩

/-- 段調整と最終修正を、元の指定境界の退化三角形を保持して貼り合わせる。 -/
def kanAdjointCanonicalEvaluationComposite (n : ℕ) :
    { C : PointedMapping.BasedPathComposite
        (kanAdjointTracedBoundaryCoordinate X Y φ j n).interval
        (kanAdjointCanonicalCorrectionInterval X Y φ j n).val //
      C.path.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (kanAdjointParameterTarget X Y n)).right =
          (kanAdjointTracedBoundaryInterval X Y φ j n).path ∧
      SSet.yonedaEquiv.symm C.triangle.simplex ≫
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (kanAdjointParameterTarget X Y n)).right =
        SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId
          (kanAdjointTracedBoundaryInterval X Y φ j n).edge).simplex } := by
  let targetKan : KanComplex (kanAdjointParameterTarget X Y n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let P := (kanAdjointTracedBoundaryCoordinate X Y φ j n).interval
  let R := kanAdjointTracedBoundaryInterval X Y φ j n
  have hP : P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (kanAdjointParameterTarget X Y n)).right =
      R.path := by
    apply PointedMapping.VerticalPath.path_restriction_eq_of_homotopy
    rw [KanAdjointBoundaryCoordinate.interval_h]
    exact kanAdjointTracedBoundaryCoordinate_comparison_boundary X Y φ j n
  let hex := PointedMapping.exists_based_composite_over_restriction j P
    (kanAdjointCanonicalCorrectionInterval X Y φ j n).val R hP
    (kanAdjointCanonicalCorrectionInterval X Y φ j n).property
  exact ⟨hex.choose, hex.choose_spec⟩

/-- 元の座標から最終座標への実ホモトピーは、境界で選んだ H_n そのものになる。 -/
lemma kanAdjointCanonicalRelativeComparison_evaluation_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy (φ ≫ kanAdjointParameterLeft X Y n).right
        (kanAdjointCanonicalRelativeComparison X Y φ j ≫
          pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        (kanAdjointTracedBoundaryHomotopy X Y φ j n).h := by
  let C := kanAdjointCanonicalEvaluationComposite X Y φ j n
  exact ⟨C.val.path.homotopy, C.val.path.homotopy_base,
    PointedMapping.VerticalPath.homotopy_restriction_eq_of_path C.val.path
      (kanAdjointTracedBoundaryInterval X Y φ j n) j C.property.1⟩

/-- BF 射影後の段座標でも、同じ元の境界ホモトピーを厳密に保持する。 -/
lemma kanAdjointCanonicalBFComparison_projected_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy (φ ≫ kanAdjointParameterLeft X Y n).right
        ((kanAdjointCanonicalBFComparison X Y φ j ≫
          pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
          PointedObject.basedHomMap (X.level n).space
            ((OmegaSpectrum.signedLoopProjection Y).app n)).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        (kanAdjointTracedBoundaryHomotopy X Y φ j n).h := by
  rw [kanAdjointCanonicalBFComparison_projected_evaluation]
  exact kanAdjointCanonicalRelativeComparison_evaluation_homotopy X Y φ j n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
