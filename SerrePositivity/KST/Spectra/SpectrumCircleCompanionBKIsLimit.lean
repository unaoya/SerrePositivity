module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionBKCoherentCone
public import SerrePositivity.KST.Spectra.SectionConePointComparison
public import SerrePositivity.KST.Spectra.SpectrumCircleBKPointLoopCone

/-!
概要：元の companion の coherent 錐の極限性を、既存の元の切断点の辺から導く。
方針：同じ固定図式・固定頂点の切断空間の辺を、錐全体の関手頂点の同型へ送る。
規約：頂点の一致だけでは判定しない。使われ方：元の円評価錐との符号を保持した比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance companionBKIsLimitSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance companionBKIsLimitHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- 元の companion の切断点から復元した元の錐は、実際の Sp の極限錐。 -/
lemma circleCompanionBKCoherentCone_isLimit (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (circleCompanionBKCoherentCone z) := by
  have h := SectionConePoint.isLimit_iff_of_edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
      (nativeCotensorInput PointedSimplicialSet.circle z).val))
    (circleCompanionConeSectionPointEdge z)
  exact h.mpr (circleBKCoherentCone_isLimit
    (nativeCotensorInput PointedSimplicialSet.circle z).val)

/-- 元の companion 錐を、元の円評価四角形の固定ホーンの図式へ移したもの。 -/
def circleCompanionBKPointLoopCone (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val) :=
  (DiagramLimitTransport.restrict (circleCompanionBKCoherentCone z)
    CospanShape.strictCospanHornIso.inv).cast
      (CospanShape.strictDiagram_eq
        (fromPoint (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (fromPoint (nativeCotensorInput PointedSimplicialSet.circle z).val))

/-- 固定ホーン上でも、元の companion 錐は元の円 cotensor を頂点に持つ。 -/
lemma circleCompanionBKPointLoopCone_vertex (z : Sp.{u} _⦋0⦌) :
    (circleCompanionBKPointLoopCone z).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  rw [circleCompanionBKPointLoopCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast,
    DiagramLimitTransport.vertex_restrict, circleCompanionBKCoherentCone_vertex]

/-- 元の固定ホーンの図式上の、実際の companion の錐の極限性。 -/
lemma circleCompanionBKPointLoopCone_isLimit (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (circleCompanionBKPointLoopCone z) := by
  let D := pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val
  let i := CospanShape.strictCospanHornIso.{u, u + 1}.inv
  have restrictionTrivial : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) i) :=
    DiagramLimitTransport.restriction_trivial (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) i
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso CospanShape.strictCospanHornIso.symm)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) i)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (DiagramLimitTransport.restrict (circleCompanionBKCoherentCone z) i) :=
    (e.isTerminalVertex_iff _).1 (circleCompanionBKCoherentCone_isLimit z)
  exact hc.cast (CospanShape.strictDiagram_eq
    (fromPoint (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (fromPoint (nativeCotensorInput PointedSimplicialSet.circle z).val))

end SerrePositivity.KST.Spectra.OmegaSpectrum
