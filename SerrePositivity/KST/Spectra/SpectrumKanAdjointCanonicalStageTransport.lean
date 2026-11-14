module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedStructureProjection
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.ThreeEdgeTransportRelabel
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTraceContraction

/-!
概要：具体的な非零境界の段射から三辺輸送を行い、その境界を保存済みの帰納三角形へ照合する。
方針：三辺の区間射影の厳密式を使い、元の二つの輸送三角形の端点表示だけを直す。
規約：二次元の入力を仮定しない。使われ方：実際の境界輸送 loop の恒等性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A)

/-- 境界の次段比較を制限し、厳密可換式で終点をそろえた元の区間。 -/
def kanAdjointCanonicalBoundaryLeft (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint
      ((KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).level
        (n + 1)).space)
      (X.sigma n ≫ kanAdjointParameterStage X Y (j ≫ φ) (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ (kanAdjointTracedParameterHom X Y (j ≫ φ)).app n ≫
        (KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) :=
  ((kanAdjointTracedStageComparison X Y (j ≫ φ) (n + 1)).pre (X.sigma n)).changeEndpoints
    rfl ((kanAdjointTracedParameterHom X Y (j ≫ φ)).comm n)

/-- 終点表示を直しても、次段制限の元の一次単体は変更しない。 -/
lemma kanAdjointCanonicalBoundaryLeft_edge (n : ℕ) :
    (kanAdjointCanonicalBoundaryLeft X Y φ j n).edge.edge =
      ((kanAdjointTracedStageComparison X Y (j ≫ φ) (n + 1)).pre (X.sigma n)).edge.edge :=
  PointedMapping.VerticalPath.changeEndpoints_edge_value
    ((kanAdjointTracedStageComparison X Y (j ≫ φ) (n + 1)).pre (X.sigma n)) rfl
    ((kanAdjointTracedParameterHom X Y (j ≫ φ)).comm n)

/-- 境界の前段比較を同じ懸垂と構造射で移した区間。 -/
def kanAdjointCanonicalBoundaryRight (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint
      ((KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).level
        (n + 1)).space)
      (PointedSimplicialSet.circle.{u} ◁ kanAdjointParameterStage X Y (j ≫ φ) n ≫
        (KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)
      (PointedSimplicialSet.circle.{u} ◁ (kanAdjointTracedParameterHom X Y (j ≫ φ)).app n ≫
        (KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) :=
  (kanAdjointTracedStageComparison X Y (j ≫ φ) n).suspension.forgetProjection.basedPost
    ((KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)

/-- 境界の三辺は、帰納構成で保存した同じ実三角形をなす。 -/
def kanAdjointCanonicalBoundaryTriangle (n : ℕ) :
    SSet.Edge.CompStruct (kanAdjointTracedStructureInterval X Y (j ≫ φ) n).edge
      (kanAdjointCanonicalBoundaryRight X Y φ j n).edge
      (kanAdjointCanonicalBoundaryLeft X Y φ j n).edge := by
  let t := kanAdjointTracedStructureTriangle X Y (j ≫ φ) n
  exact { simplex := t.simplex, d₀ := t.d₀, d₁ := t.d₁, d₂ := t.d₂ }

variable [Mono j.right]

/-- 次段比較の射影の一次単体を、境界の同じ制限区間へ照合する。 -/
lemma kanAdjointCanonicalLeft_projection_edge (n : ℕ) :
    (((kanAdjointTracedAdjustedStageInterval X Y φ j (n + 1)).pre (X.sigma n)).edge.map
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right).edge = (kanAdjointCanonicalBoundaryLeft X Y φ j n).edge.edge := by
  rw [kanAdjointCanonicalBoundaryLeft_edge]
  exact PointedMapping.VerticalPath.projection_edge_value
    ((kanAdjointTracedAdjustedStageInterval X Y φ j (n + 1)).pre (X.sigma n))
    ((kanAdjointTracedStageComparison X Y (j ≫ φ) (n + 1)).pre (X.sigma n))
    ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
    (kanAdjointTracedNextCorrection_projection_path X Y φ j n)

omit [Mono j.right] in
/-- 元の構造比較の射影の一次単体を、境界の同じ構造区間へ照合する。 -/
lemma kanAdjointCanonicalMiddle_projection_edge (n : ℕ) :
    ((kanAdjointTracedStructureInterval X Y φ n).edge.map
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right).edge =
      (kanAdjointTracedStructureInterval X Y (j ≫ φ) n).edge.edge :=
  PointedMapping.VerticalPath.projection_edge_value
    (kanAdjointTracedStructureInterval X Y φ n)
    (kanAdjointTracedStructureInterval X Y (j ≫ φ) n)
    ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
    (kanAdjointTracedStructureInterval_projection_path X Y φ j n)

/-- 前段比較の射影の一次単体を、境界の同じ構造像区間へ照合する。 -/
lemma kanAdjointCanonicalRight_projection_edge (n : ℕ) :
    (((kanAdjointTracedAdjustedStageInterval X Y φ j n).suspension.forgetProjection.basedPost
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).edge.map
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right).edge = (kanAdjointCanonicalBoundaryRight X Y φ j n).edge.edge :=
  PointedMapping.VerticalPath.projection_edge_value
    ((kanAdjointTracedAdjustedStageInterval X Y φ j n).suspension.forgetProjection.basedPost
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n))
    ((kanAdjointTracedStageComparison X Y (j ≫ φ) n).suspension.forgetProjection.basedPost
      ((KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).sigma n))
    ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
    (kanAdjointTracedPreviousCorrection_projection_path X Y φ j n)

/-- 調整済み段射の構造比較を、元の三辺と二つの実三角形で構成する。 -/
def kanAdjointCanonicalStageTransport (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport
      ((kanAdjointTracedAdjustedStageInterval X Y φ j (n + 1)).pre (X.sigma n)).edge
      (kanAdjointTracedStructureInterval X Y φ n).edge
      ((kanAdjointTracedAdjustedStageInterval X Y φ j n).suspension.forgetProjection.basedPost
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).edge := by
  let homKan : KanComplex (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level
      (n + 1)).space).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.choose _ _ _

/-- 同じ輸送辺を、そのまま実際の調整済み構造区間へ戻す。 -/
def kanAdjointCanonicalStageStructurePath (n : ℕ) :
    KanAdjointBoundaryStructurePath X Y φ j (kanAdjointTracedBoundary X Y φ j)
      (kanAdjointTracedBoundaryHomotopy X Y φ j)
      (kanAdjointTracedBoundaryCoordinate X Y φ j) n :=
  PointedMapping.basedPathOfEdge (kanAdjointCanonicalStageTransport X Y φ j n).transported

/-- 輸送三角形を境界へ写し、その三辺を保存済み帰納三角形の同じ一次単体へ直す。 -/
def kanAdjointCanonicalBoundaryTransport (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport (kanAdjointCanonicalBoundaryLeft X Y φ j n).edge
      (kanAdjointTracedStructureInterval X Y (j ≫ φ) n).edge
      (kanAdjointCanonicalBoundaryRight X Y φ j n).edge := by
  let q := (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))).right
  let D := (kanAdjointCanonicalStageTransport X Y φ j n).map q
  exact D.relabel _ _ _ (kanAdjointCanonicalLeft_projection_edge X Y φ j n)
    (kanAdjointCanonicalMiddle_projection_edge X Y φ j n)
    (kanAdjointCanonicalRight_projection_edge X Y φ j n)

/-- 境界の閉じた輸送辺の類は、実際の帰納三角形により恒等射。 -/
lemma kanAdjointCanonicalBoundaryTransport_identity (n : ℕ) :
    SSet.HomotopyCategory.homMk
        (kanAdjointCanonicalBoundaryTransport X Y φ j n).transported =
      𝟙 (SSet.HomotopyCategory.mk (PointedMapping.familyVertex
        (PointedSimplicialSet.circle.{u} ◁ (kanAdjointTracedParameterHom X Y (j ≫ φ)).app n ≫
          (KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).sigma n))) := by
  let homKan : KanComplex (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    ((KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).level
      (n + 1)).space).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact (kanAdjointCanonicalBoundaryTransport X Y φ j n).transported_homMk_eq_id
    (kanAdjointCanonicalBoundaryTriangle X Y φ j n)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
