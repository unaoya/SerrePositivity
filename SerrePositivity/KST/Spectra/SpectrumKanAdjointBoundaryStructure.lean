module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointBoundaryCoordinates
public import SerrePositivity.KST.Spectra.PointedPathProjectionContraction

/-!
概要：非零境界へ調整した Kan 随伴の段射の構造比較と、その射影の収縮の条件。
方針：元の構造成分式を調整区間で移し、射影の両端点固定収縮を持ち上げて垂直化する。
規約：収縮を成分一致から仮定しない。使われ方：非零境界の全列の相対厳密化。
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
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A)
  (c : B ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence))
  (H : ∀ n, KanAdjointBoundaryHomotopy X Y φ j c n)
  (s : ∀ n, KanAdjointBoundaryCoordinate X Y φ j c n (H n))

/-- 境界を調整した段射も、元の構造条件を写像成分で満たす。 -/
lemma kanAdjointBoundaryStructure_component (n : ℕ) :
    PointedMapping.componentOf (PointedSimplicialSet.circle.{u} ◁ (s n).stage ≫
      (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) =
    PointedMapping.componentOf (X.sigma n ≫ (s (n + 1)).stage) := by
  have hl := PointedMapping.componentOf_comp_right (s n).component
    (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)
  have hr := PointedMapping.componentOf_comp_right (s (n + 1)).component
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)
  have hm := PointedMapping.componentOf_comp_left (kanAdjointParameterLeft_condition X Y n) φ
  have hc := PointedMapping.componentOf_transpose (hl.trans (hm.trans hr.symm))
  have hs := transpose_step X (KanSequence.signedLoopTail Y.toKanSequence) A n
    (s n).coordinate
  have ht := transpose_restriction X (KanSequence.signedLoopTail Y.toKanSequence) A n
    (s (n + 1)).coordinate
  rw [hs, ht] at hc
  exact hc

/-- 非零境界への調整後、構造比較の両端は指定境界へ厳密に同じ射を与える。 -/
lemma kanAdjointBoundaryStructure_projection_endpoints (n : ℕ) :
    (PointedSimplicialSet.circle.{u} ◁ (s n).stage ≫
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) ≫
      (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1) =
    (X.sigma n ≫ (s (n + 1)).stage) ≫
      (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
        (n + 1) := by
  let q := KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)
  let b := homOfParameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) B c
  change (PointedSimplicialSet.circle.{u} ◁ (s n).stage ≫ _) ≫ q.app (n + 1) = _
  rw [Category.assoc, ← q.comm n, ← Category.assoc, ← whiskerLeft_comp,
    (s n).projection]
  change PointedSimplicialSet.circle.{u} ◁ b.app n ≫ _ = _
  rw [b.comm n, Category.assoc, (s (n + 1)).projection]
  rfl

/-- 調整済み段射の元の構造比較の、選択前の実際の基点固定区間の型。 -/
abbrev KanAdjointBoundaryStructurePath (n : ℕ) :=
  PointedMapping.VerticalPath (PointedObject.toPoint
    ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level
      (n + 1)).space)
    (X.sigma n ≫ (s (n + 1)).stage)
    (PointedSimplicialSet.circle.{u} ◁ (s n).stage ≫
      (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)

/-- 調整済み段射の構造比較は、実際の基点固定区間として実現できる。 -/
def kanAdjointBoundaryStructurePath (n : ℕ) :
    KanAdjointBoundaryStructurePath X Y φ j c H s n :=
  PointedMapping.basedPathOfComponent
    (kanAdjointBoundaryStructure_component X Y φ j c H s n).symm

/-- 構造区間の射影を両端点を固定して収縮するための、明示した二次元の入力。 -/
structure KanAdjointBoundaryStructureContraction (n : ℕ)
    (P : KanAdjointBoundaryStructurePath X Y φ j c H s n) where
  homotopy : SSet.Homotopy
    (P.path ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right)
    (SSet.const (PointedMapping.familyVertex ((X.sigma n ≫ (s (n + 1)).stage) ≫
      (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))))
  boundary : (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ homotopy.h =
    fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫
      P.path ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right

/-- 二次元の射影収縮から、元の制限を全区間で固定する構造比較を回収する。 -/
def kanAdjointBoundaryVerticalStructurePath [Mono j.right] (n : ℕ)
    (P : KanAdjointBoundaryStructurePath X Y φ j c H s n)
    (K : KanAdjointBoundaryStructureContraction X Y φ j c H s n P) :
    PointedMapping.VerticalPath
      ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app (n + 1))
      (X.sigma n ≫ (s (n + 1)).stage)
      (PointedSimplicialSet.circle.{u} ◁ (s n).stage ≫
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) :=
  (PointedMapping.exists_vertical_path_of_projection_contraction _
    (mappingPre_level_horn_rlp j (KanSequence.signedLoopTail Y.toKanSequence) (n + 1))
    P K.homotopy K.boundary).choose

end SerrePositivity.KST.Spectra.RawSpectrumMapping
