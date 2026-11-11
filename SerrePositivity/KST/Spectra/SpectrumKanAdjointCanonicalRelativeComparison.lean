module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCanonicalStageTransport

/-!
概要：具体的な帰納境界のトレース恒等性から収縮を構成し、非零境界を保つ全列比較を得る。
方針：同じ輸送一次単体を射影 loop と照合し、実収縮・垂直化・相対厳密化へ順に渡す。
規約：収縮やトレース恒等性を入力しない。使われ方：元の Kan 随伴比較の相対構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 境界輸送の loop と射影 loop を照合する、元の一次単体の等式。 -/
lemma kanAdjointCanonicalBoundaryTransport_edge (n : ℕ) :
    (kanAdjointCanonicalBoundaryTransport X Y φ j n).transported.edge =
      ((kanAdjointCanonicalStageTransport X Y φ j n).transported.map
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
          ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
            (n + 1))).right).edge := rfl

/-- 実際の構造区間の射影そのものを持つ loop 単体。 -/
def kanAdjointCanonicalProjectionLoop (n : ℕ) :=
  PointedMapping.projectionLoop
    ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
    (kanAdjointCanonicalStageStructurePath X Y φ j n)
    (kanAdjointBoundaryStructure_projection_endpoints X Y φ j (kanAdjointTracedBoundary X Y φ j)
      (kanAdjointTracedBoundaryHomotopy X Y φ j) (kanAdjointTracedBoundaryCoordinate X Y φ j) n)

/-- 同じ射影区間のトレースは、保存済み境界三角形により実際に恒等射を表す。 -/
lemma kanAdjointCanonicalProjectionLoop_identity (n : ℕ) :
    SSet.HomotopyCategory.homMk
        (FundamentalLoop.edge (kanAdjointCanonicalProjectionLoop X Y φ j n)) =
      𝟙 (SSet.HomotopyCategory.mk (PointedMapping.familyVertex
        ((X.sigma n ≫ (kanAdjointTracedBoundaryCoordinate X Y φ j (n + 1)).stage) ≫
          (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
            (n + 1)))) := by
  have he : (FundamentalLoop.edge (kanAdjointCanonicalProjectionLoop X Y φ j n)).edge =
      (kanAdjointCanonicalBoundaryTransport X Y φ j n).transported.edge := by
    let q := (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
        (n + 1))).right
    rw [kanAdjointCanonicalBoundaryTransport_edge]
    change SSet.yonedaEquiv
      ((kanAdjointCanonicalStageStructurePath X Y φ j n).path ≫ q) =
        q.app _ (kanAdjointCanonicalStageTransport X Y φ j n).transported.edge
    rw [SSet.yonedaEquiv_comp]
    change q.app _ (SSet.yonedaEquiv (SSet.yonedaEquiv.symm
      (kanAdjointCanonicalStageTransport X Y φ j n).transported.edge)) = _
    rw [Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.loop_identity_congr he
    (kanAdjointCanonicalBoundaryTransport_identity X Y φ j n)

/-- 元の帰納境界の実三角形から、構造射影の実際の両端点固定収縮を構成する。 -/
def kanAdjointCanonicalStructureContraction (n : ℕ) :
    KanAdjointBoundaryStructureContraction X Y φ j (kanAdjointTracedBoundary X Y φ j)
      (kanAdjointTracedBoundaryHomotopy X Y φ j) (kanAdjointTracedBoundaryCoordinate X Y φ j) n
      (kanAdjointCanonicalStageStructurePath X Y φ j n) := by
  let homKan : KanComplex (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    ((KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).level
      (n + 1)).space).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let hex := exists_loop_contraction_of_homMk_eq_id (kanAdjointCanonicalProjectionLoop X Y φ j n)
    (kanAdjointCanonicalProjectionLoop_identity X Y φ j n)
  exact ⟨hex.choose, hex.choose_spec⟩

/-- 元の入力から、実際の帰納非零境界を厳密に保つ全列の比較を構成する。 -/
def kanAdjointCanonicalRelativeComparison :
    A ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  kanAdjointBoundaryComparison X Y φ j (kanAdjointTracedBoundary X Y φ j)
    (kanAdjointTracedBoundaryHomotopy X Y φ j) (kanAdjointTracedBoundaryCoordinate X Y φ j)
    (kanAdjointCanonicalStageStructurePath X Y φ j)
    (kanAdjointCanonicalStructureContraction X Y φ j)

/-- 実際の全列の比較は、部分対象上の同じ帰納構成の非零境界へ厳密に制限される。 -/
lemma kanAdjointCanonicalRelativeComparison_boundary :
    j ≫ kanAdjointCanonicalRelativeComparison X Y φ j = kanAdjointTracedBoundary X Y φ j :=
  kanAdjointBoundaryComparison_boundary X Y φ j (kanAdjointTracedBoundary X Y φ j)
    (kanAdjointTracedBoundaryHomotopy X Y φ j) (kanAdjointTracedBoundaryCoordinate X Y φ j)
    (kanAdjointCanonicalStageStructurePath X Y φ j)
    (kanAdjointCanonicalStructureContraction X Y φ j)

/-- 各段の比較は、同じ元の Kan 随伴座標の成分を保つ。 -/
lemma kanAdjointCanonicalRelativeComparison_evaluation_component (n : ℕ) :
    PointedMapping.componentOf (kanAdjointCanonicalRelativeComparison X Y φ j ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) =
      PointedMapping.componentOf (φ ≫ kanAdjointParameterLeft X Y n) :=
  kanAdjointBoundaryComparison_evaluation_component X Y φ j (kanAdjointTracedBoundary X Y φ j)
    (kanAdjointTracedBoundaryHomotopy X Y φ j) (kanAdjointTracedBoundaryCoordinate X Y φ j)
    (kanAdjointCanonicalStageStructurePath X Y φ j)
    (kanAdjointCanonicalStructureContraction X Y φ j) n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
