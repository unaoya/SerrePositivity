module

public import SerrePositivity.KST.Spectra.SequenceParameterRelativeTracedRectification
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCanonicalCoordinateHomotopy

/-!
概要：具体的な非零境界の上で、元の Kan 随伴比較を実垂直区間と構造三角形つきで厳密化する。
方針：構成済みの射影収縮から実構造区間を回収し、三角形を保持する相対帰納構成へ入力する。
規約：全列のホモトピーは未主張。使われ方：元の比較の段方向の高次整合性の回収。
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

/-- 元の境界収縮から回収する、調整済み段射の実垂直構造区間。 -/
def kanAdjointCanonicalVerticalStructurePath (n : ℕ) :
    PointedMapping.VerticalPath
      ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
      (X.sigma n ≫ (kanAdjointTracedBoundaryCoordinate X Y φ j (n + 1)).stage)
      (PointedSimplicialSet.circle.{u} ◁ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage ≫
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) :=
  kanAdjointBoundaryVerticalStructurePath X Y φ j (kanAdjointTracedBoundary X Y φ j)
    (kanAdjointTracedBoundaryHomotopy X Y φ j) (kanAdjointTracedBoundaryCoordinate X Y φ j) n
    (kanAdjointCanonicalStageStructurePath X Y φ j n)
    (kanAdjointCanonicalStructureContraction X Y φ j n)

/-- 同じ実垂直区間と構造三角形を保持して厳密化した、cotensor 値の列射。 -/
def kanAdjointRelativeTracedParameterHom :
    KanSequence.Hom X.toKanSequence
      (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)) :=
  relativeTracedParameterHom X (KanSequence.signedLoopTail Y.toKanSequence) j
    (kanAdjointTracedBoundary X Y φ j)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection)
    (kanAdjointCanonicalVerticalStructurePath X Y φ j)

/-- 実構造三角形を保持する相対帰納構成から得る、元の全列の比較族。 -/
def kanAdjointRelativeTracedComparison :
    A ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  parameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
    (kanAdjointRelativeTracedParameterHom X Y φ j)

/-- 元の具体的な非零帰納境界は、全列で厳密に保持する。 -/
lemma kanAdjointRelativeTracedComparison_boundary :
    j ≫ kanAdjointRelativeTracedComparison X Y φ j = kanAdjointTracedBoundary X Y φ j :=
  rectifyParameterRelativeTraced_boundary X (KanSequence.signedLoopTail Y.toKanSequence) j
    (kanAdjointTracedBoundary X Y φ j)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection)
    (kanAdjointCanonicalVerticalStructurePath X Y φ j)

/-- 元の構造区間・前段比較・次段比較の制限を持つ、同じ相対構造三角形。 -/
def kanAdjointRelativeTracedTriangle (n : ℕ) :=
  KanSequence.relativeTracedComparison_triangle (X := X.toKanSequence)
    (Y := KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))
    (Z := KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence))
    X.sigma_mono (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence))
    (mappingPre_level_horn_rlp j (KanSequence.signedLoopTail Y.toKanSequence))
    (homOfParameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) B
      (kanAdjointTracedBoundary X Y φ j))
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection)
    (kanAdjointCanonicalVerticalStructurePath X Y φ j) n

/-- 保存した実修正区間を転置した、非零境界を固定する最終段座標への区間。 -/
def kanAdjointRelativeTracedCorrectionInterval (n : ℕ) :
    { P : PointedMapping.VerticalPath (PointedObject.toPoint (kanAdjointParameterTarget X Y n))
        (kanAdjointTracedBoundaryCoordinate X Y φ j n).coordinate
        (kanAdjointRelativeTracedComparison X Y φ j ≫
          pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) //
      P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (kanAdjointParameterTarget X Y n)).right =
        SSet.const (PointedMapping.familyVertex (kanAdjointTracedBoundary X Y φ j ≫
          pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n)) } := by
  let Q := relativeTracedParameterEvaluationInterval X
    (KanSequence.signedLoopTail Y.toKanSequence) j (kanAdjointTracedBoundary X Y φ j)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection)
    (kanAdjointCanonicalVerticalStructurePath X Y φ j) n
  let R := Q.val.changeEndpoints (PointedMapping.transpose_transpose
    (kanAdjointTracedBoundaryCoordinate X Y φ j n).coordinate).symm rfl
  exact ⟨R, Q.property⟩

/-- 元の段座標からの実ホモトピーも、指定済み非零境界区間そのものを保持する。 -/
lemma kanAdjointRelativeTracedComparison_evaluation_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy (φ ≫ kanAdjointParameterLeft X Y n).right
        (kanAdjointRelativeTracedComparison X Y φ j ≫
          pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        (kanAdjointTracedBoundaryHomotopy X Y φ j n).h := by
  let targetKan : KanComplex (kanAdjointParameterTarget X Y n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let P := (kanAdjointTracedBoundaryCoordinate X Y φ j n).interval
  let Q := kanAdjointRelativeTracedCorrectionInterval X Y φ j n
  let R := kanAdjointTracedBoundaryInterval X Y φ j n
  have hP : P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (kanAdjointParameterTarget X Y n)).right =
      R.path := by
    apply PointedMapping.VerticalPath.path_restriction_eq_of_homotopy
    rw [KanAdjointBoundaryCoordinate.interval_h]
    exact kanAdjointTracedBoundaryCoordinate_comparison_boundary X Y φ j n
  obtain ⟨C, hC, _⟩ := PointedMapping.exists_based_composite_over_restriction j P Q.val R hP
    Q.property
  exact ⟨C.path.homotopy, C.path.homotopy_base,
    PointedMapping.VerticalPath.homotopy_restriction_eq_of_path C.path R j hC⟩

end SerrePositivity.KST.Spectra.RawSpectrumMapping
