module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStructureIntervals
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointBoundaryStructure
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.ThreeEdgeTransport

/-!
概要：元の構造比較と段調整の三つの区間から、調整済み構造区間を二つの三角形つきで作る。
方針：三辺輸送を元のパラメータ Hom で行い、同じ辺を転置して元の列の構造 Hom へ移す。
規約：境界トレースは元の三角形の像。使われ方：構造射影の実際の収縮の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A)
  (c : B ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence))
  (H : ∀ n, KanAdjointBoundaryHomotopy X Y φ j c n)
  (s : ∀ n, KanAdjointBoundaryCoordinate X Y φ j c n (H n))

/-- 三つの元の区間を置く、懸垂源からの構造 Hom。 -/
abbrev kanAdjointBoundaryTraceTarget (n : ℕ) : PointedSimplicialSet.{u} :=
  PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space

/-- 一段先の段調整区間を、元の構造射への制限で移す。 -/
def kanAdjointBoundaryTraceLeft (n : ℕ) :=
  (s (n + 1)).interval.basedPost
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)

/-- 当段の段調整区間を、元の構造 Hom の step で移す。 -/
def kanAdjointBoundaryTraceRight (n : ℕ) :=
  (s n).interval.basedPost (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)

/-- 元の三つの区間からの輸送辺と、その境界へ写す二つの実三角形。 -/
def kanAdjointBoundaryTransport (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport (kanAdjointBoundaryTraceLeft X Y φ j c H s n).edge
      (kanAdjointParameterStructureInterval X Y φ n).edge
      (kanAdjointBoundaryTraceRight X Y φ j c H s n).edge := by
  let targetKan : KanComplex (kanAdjointBoundaryTraceTarget X Y n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let pathSpaceKan :
      KanComplex (PointedObject.basedHom A (kanAdjointBoundaryTraceTarget X Y n)).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport.choose _ _ _

/-- 同じ輸送辺を転置して得る、調整済み段射の実際の構造区間。 -/
def kanAdjointBoundaryTracedStructurePath (n : ℕ) :
    KanAdjointBoundaryStructurePath X Y φ j c H s n := by
  let P := (PointedMapping.basedPathOfEdge
    (kanAdjointBoundaryTransport X Y φ j c H s n).transported).basedTranspose
  have hr := transpose_restriction X (KanSequence.signedLoopTail Y.toKanSequence) A n
    (s (n + 1)).coordinate
  have hl := transpose_step X (KanSequence.signedLoopTail Y.toKanSequence) A n
    (s n).coordinate
  exact P.changeEndpoints hr.symm hl.symm

/-- 元の列の構造区間も、選択済みの同じ輸送辺の交換同型による像そのもの。 -/
lemma kanAdjointBoundaryTracedStructurePath_path (n : ℕ) :
    (kanAdjointBoundaryTracedStructurePath X Y φ j c H s n).path =
      SSet.yonedaEquiv.symm (kanAdjointBoundaryTransport X Y φ j c H s n).transported.edge ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right := rfl

/-- 構造区間の射影は、同じ輸送辺を境界へ制限してから交換した区間に厳密に一致する。 -/
lemma kanAdjointBoundaryTracedStructurePath_projection (n : ℕ) :
    (kanAdjointBoundaryTracedStructurePath X Y φ j c H s n).path ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right =
    (SSet.yonedaEquiv.symm (kanAdjointBoundaryTransport X Y φ j c H s n).transported.edge ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j (kanAdjointBoundaryTraceTarget X Y n)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left j (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  have he := congrArg Under.Hom.right h.symm
  change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j (kanAdjointBoundaryTraceTarget X Y n) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right at he
  rw [kanAdjointBoundaryTracedStructurePath_path, Category.assoc]
  simpa only [Category.assoc] using congrArg (SSet.yonedaEquiv.symm
    (kanAdjointBoundaryTransport X Y φ j c H s n).transported.edge ≫ ·) he

/-- 構造比較の境界の類は、指定段調整・元の係数区間・指定段調整の同じ三つの像で計算する。 -/
lemma kanAdjointBoundaryTransport_boundary_trace (n : ℕ) :
    SSet.HomotopyCategory.homMk
        ((kanAdjointBoundaryTraceLeft X Y φ j c H s n).edge.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j (kanAdjointBoundaryTraceTarget X Y n))) ≫
      SSet.HomotopyCategory.homMk
        ((kanAdjointBoundaryTransport X Y φ j c H s n).transported.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j (kanAdjointBoundaryTraceTarget X Y n))) =
    SSet.HomotopyCategory.homMk
        ((kanAdjointParameterStructureInterval X Y φ n).edge.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j (kanAdjointBoundaryTraceTarget X Y n))) ≫
      SSet.HomotopyCategory.homMk
        ((kanAdjointBoundaryTraceRight X Y φ j c H s n).edge.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j (kanAdjointBoundaryTraceTarget X Y n))) :=
  (kanAdjointBoundaryTransport X Y φ j c H s n).map_trace _

end SerrePositivity.KST.Spectra.RawSpectrumMapping
