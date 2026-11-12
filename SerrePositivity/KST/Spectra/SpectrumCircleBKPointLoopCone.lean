module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKIsLimit
public import SerrePositivity.KST.Spectra.StrictCospanHorn
public import SerrePositivity.KST.Spectra.DiagramLimitExistenceTransport

/-!
概要：円 cotensor の元の BK 錐を、固定ホーン図式の実際の ∞ 極限錐へ移す。
方針：通常の cospan の nerve と二辺のホーンの形状同型に沿って制限する。
規約：元の cotensor 頂点と固定された一点 → Y ← 一点の図式を保つ。
使われ方：元の円評価四角形との錐全体の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circlePointLoopConeSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance circlePointLoopConeHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- 元の円評価の BK 切断点による、固定ホーン図式上の実際の cotensor 錐。 -/
def circleBKPointLoopCone (Y : OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (pointLoopCospan Y) :=
  (DiagramLimitTransport.restrict (circleBKCoherentCone Y)
    CospanShape.strictCospanHornIso.inv).cast
      (CospanShape.strictDiagram_eq (fromPoint Y) (fromPoint Y))

/-- 形状同型による制限後も、頂点は元の円 cotensor の標準頂点そのもの。 -/
lemma circleBKPointLoopCone_vertex (Y : OmegaSpectrum.{u}) :
    (circleBKPointLoopCone Y).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle Y) := by
  rw [circleBKPointLoopCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, DiagramLimitTransport.vertex_restrict,
    circleBKCoherentCone_vertex]

/-- 固定された一点 → Y ← 一点の図式に対する、元の円 cotensor の実際の極限錐。 -/
lemma circleBKPointLoopCone_isLimit (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (circleBKPointLoopCone Y) := by
  let D := pointLoopDiagram Y
  let i := CospanShape.strictCospanHornIso.{u, u + 1}.inv
  have restrictionTrivial : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) i) :=
    DiagramLimitTransport.restriction_trivial (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) i
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso CospanShape.strictCospanHornIso.symm)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) i)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (DiagramLimitTransport.restrict (circleBKCoherentCone Y) i) :=
    (e.isTerminalVertex_iff _).1 (circleBKCoherentCone_isLimit Y)
  exact hc.cast (CospanShape.strictDiagram_eq (fromPoint Y) (fromPoint Y))

end SerrePositivity.KST.Spectra.OmegaSpectrum
