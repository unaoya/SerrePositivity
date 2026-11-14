module

public import SerrePositivity.KST.Spectra.SpectrumCircleSquareCospan
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitIsLimit
public import SerrePositivity.KST.Spectra.StrictCospanHorn
public import SerrePositivity.KST.Spectra.DiagramLimitExistenceTransport
public import SerrePositivity.KST.Spectra.LoopConeSquareVertex

/-!
概要：二本とも一点からの元の射である固定 cospan の、実際の BF homotopy limit の極限錐。
方針：任意の通常の BF 図式の極限錐を二辺のホーンへ同型で制限する。
規約：円評価錐の極限性を仮定しない。使われ方：同じ固定図式上の錐の比較射の構成。
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
local instance pointLoopReferenceSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance pointLoopReferenceHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- 二本の元の一点からの射で与える、通常の小さい BF cospan 図式。 -/
def pointLoopDiagram (Y : OmegaSpectrum.{u}) : AsSmall.{u} WalkingCospan ⥤ OmegaSpectrum.{u} :=
  AsSmall.down ⋙ cospan (fromPoint Y) (fromPoint Y)

/-- 固定 cospan に対する、元の BF homotopy limit を頂点とする参照錐。 -/
def pointLoopReferenceCone (Y : OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (pointLoopCospan Y) :=
  (DiagramLimitTransport.restrict (homotopyLimitCoherentCone (pointLoopDiagram Y))
    CospanShape.strictCospanHornIso.inv).cast
      (CospanShape.strictDiagram_eq (fromPoint Y) (fromPoint Y))

/-- 参照錐の頂点は元の BF homotopy limit の標準頂点に厳密一致。 -/
lemma pointLoopReferenceCone_vertex (Y : OmegaSpectrum.{u}) :
    (pointLoopReferenceCone Y).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (homotopyLimit (pointLoopDiagram Y)) := by
  rw [pointLoopReferenceCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, DiagramLimitTransport.vertex_restrict,
    homotopyLimitCoherentCone_vertex]

/-- 参照錐は、円評価錐とは独立に証明済みの実際の Sp の極限錐。 -/
lemma pointLoopReferenceCone_isLimit (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (pointLoopReferenceCone Y) := by
  let D := pointLoopDiagram Y
  let i := CospanShape.strictCospanHornIso.{u, u + 1}.inv
  have pointLoopRestrictionTrivial : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) i) :=
    DiagramLimitTransport.restriction_trivial (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) i
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso CospanShape.strictCospanHornIso.symm)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) i)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (DiagramLimitTransport.restrict (homotopyLimitCoherentCone D) i) :=
    (e.isTerminalVertex_iff _).1 (homotopyLimitCoherentCone_isLimit D)
  exact hc.cast (CospanShape.strictDiagram_eq (fromPoint Y) (fromPoint Y))

/-- 四角形から作る錐の頂点は、元の左下の頂点そのもの。 -/
lemma circlePullbackCone_vertex (z : Sp.{u} _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (nativeCircleEvaluationSquare z)).vertex =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (nativeCircleEvaluationSquare z) 0 0 := by
  have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (nativeCircleEvaluationSquare z)) =
      nativeCircleEvaluationSquare z := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone]
    rw [Iso.inv_hom_id_assoc]
  have h := coneSquare_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (nativeCircleEvaluationSquare z))
  rw [hs] at h
  exact h.symm

/-- 固定図式へ移した円評価錐の頂点は、同じ入力の元の BF cotensor。 -/
lemma nativeCirclePointLoopCone_vertex (z : Sp.{u} _⦋0⦌) :
    (nativeCirclePointLoopCone z).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  rw [nativeCirclePointLoopCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, circlePullbackCone_vertex,
    nativeCircleEvaluationSquare_source]

end SerrePositivity.KST.Spectra.OmegaSpectrum
