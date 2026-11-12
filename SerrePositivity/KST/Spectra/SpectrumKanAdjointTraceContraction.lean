module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointBoundaryTrace
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointBoundaryRectification
public import SerrePositivity.KST.Spectra.PointedProjectionLoop

/-!
概要：実際の三辺輸送で作った構造区間の射影 loop から、境界固定収縮を回収する。
方針：同じ射影区間を loop 単体へ読み、その恒等性を基本群と相対 prism で収縮へ戻す。
規約：トレースの恒等性は入力。使われ方：非零境界の相対比較の二次元入力の削減。
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
  (c : B ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence))
  (H : ∀ n, KanAdjointBoundaryHomotopy X Y φ j c n)
  (s : ∀ n, KanAdjointBoundaryCoordinate X Y φ j c n (H n))

/-- 元の三辺輸送を転置した構造区間の、同じ射影区間を持つ loop。 -/
def kanAdjointBoundaryProjectionLoop (n : ℕ) :=
  PointedMapping.projectionLoop
    ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
    (kanAdjointBoundaryTracedStructurePath X Y φ j c H s n)
    (kanAdjointBoundaryStructure_projection_endpoints X Y φ j c H s n)

/-- 元の三辺輸送による構造区間の射影 loop の類が恒等射である条件。 -/
abbrev KanAdjointBoundaryTraceIdentity (n : ℕ) :=
  SSet.HomotopyCategory.homMk
      (FundamentalLoop.edge (kanAdjointBoundaryProjectionLoop X Y φ j c H s n)) =
    𝟙 (SSet.HomotopyCategory.mk (PointedMapping.familyVertex
      ((X.sigma n ≫ (s (n + 1)).stage) ≫
        (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))))

/-- トレースの恒等性から、同じ構造区間の射影の実際の境界固定収縮を作る。 -/
def kanAdjointBoundaryTraceContraction (n : ℕ)
    (h : KanAdjointBoundaryTraceIdentity X Y φ j c H s n) :
    KanAdjointBoundaryStructureContraction X Y φ j c H s n
      (kanAdjointBoundaryTracedStructurePath X Y φ j c H s n) := by
  let hex := PointedMapping.exists_projection_contraction_of_trace_identity
    ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
    (kanAdjointBoundaryTracedStructurePath X Y φ j c H s n)
    (kanAdjointBoundaryStructure_projection_endpoints X Y φ j c H s n) h
  exact ⟨hex.choose, hex.choose_spec⟩

/-- 実際の構造区間の射影収縮の存在と、同じ loop のトレースの恒等性は同値。 -/
lemma kanAdjointBoundaryTraceContraction_nonempty_iff (n : ℕ) :
    Nonempty (KanAdjointBoundaryStructureContraction X Y φ j c H s n
      (kanAdjointBoundaryTracedStructurePath X Y φ j c H s n)) ↔
      KanAdjointBoundaryTraceIdentity X Y φ j c H s n := by
  let boundaryHomKan : KanComplex
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).level
          (n + 1)).space).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  constructor
  · rintro ⟨K⟩
    exact homMk_eq_id_of_loop_contraction (kanAdjointBoundaryProjectionLoop X Y φ j c H s n)
      K.homotopy K.boundary
  · intro h
    exact ⟨kanAdjointBoundaryTraceContraction X Y φ j c H s n h⟩

/-- 元の三辺トレースの恒等性から、指定非零境界を保つ全列の比較を構成する。 -/
def kanAdjointComparisonOfTraceIdentity [Mono j.right]
    (h : ∀ n, KanAdjointBoundaryTraceIdentity X Y φ j c H s n) :
    A ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  kanAdjointBoundaryComparison X Y φ j c H s
    (kanAdjointBoundaryTracedStructurePath X Y φ j c H s)
    (fun n ↦ kanAdjointBoundaryTraceContraction X Y φ j c H s n (h n))

/-- 回収した収縮を使う全列の比較は、元の指定した非零境界へ厳密に制限される。 -/
lemma kanAdjointComparisonOfTraceIdentity_boundary [Mono j.right]
    (h : ∀ n, KanAdjointBoundaryTraceIdentity X Y φ j c H s n) :
    j ≫ kanAdjointComparisonOfTraceIdentity X Y φ j c H s h = c :=
  kanAdjointBoundaryComparison_boundary X Y φ j c H s
    (kanAdjointBoundaryTracedStructurePath X Y φ j c H s)
    (fun n ↦ kanAdjointBoundaryTraceContraction X Y φ j c H s n (h n))

end SerrePositivity.KST.Spectra.RawSpectrumMapping
