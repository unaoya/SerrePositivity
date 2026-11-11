module

public import SerrePositivity.KST.Spectra.BasedPathSpectrumZero
public import SerrePositivity.KST.Spectra.StrictCospanHorn
public import SerrePositivity.KST.Spectra.DiagramLimitExistenceTransport
public import SerrePositivity.KST.Spectra.Limits.SpectrumHomFibrations

/-!
概要：BF path の終点 fibration と一点から作る、具体的な loop の極限錐。
方針：段ごとの厳密な引き戻しの ∞ 極限性を、二辺のホーンの形状へ制限する。
規約：頂点は実際の BF 引き戻し対象。使われ方：Sp の native な loop 四角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.BasedLoop
local instance basedLoopSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance basedLoopHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- BF path 終点の基点上の、具体的な BF 引き戻し対象。 -/
def obj (Y : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullback (basedPathProjection Y) (fromPoint Y)

/-- BF path と一点の二辺を指定した loop の図式。 -/
def diagram (Y : OmegaSpectrum.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (basedPathProjection Y)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fromPoint Y)).toTruncated

/-- 指定した二辺のホーン上の具体的な loop 錐。 -/
def cone (Y : OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (diagram Y) :=
  (DiagramLimitTransport.restrict
    (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone (basedPathProjection Y) (fromPoint Y))
    CospanShape.strictCospanHornIso.inv).cast
      (CospanShape.strictDiagram_eq (basedPathProjection Y) (fromPoint Y))

/-- 具体的な錐の頂点は、構成した BF 引き戻しそのもの。 -/
lemma cone_vertex (Y : OmegaSpectrum.{u}) :
    (cone Y).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (obj Y) := by
  rw [cone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, DiagramLimitTransport.vertex_restrict,
    _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex]
  rfl

/-- 構成した具体的な loop 錐は元の Sp の ∞ 極限。 -/
lemma cone_isLimit (Y : OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (cone Y) := by
  let d := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone (basedPathProjection Y) (fromPoint Y)
  let i := CospanShape.strictCospanHornIso.{u, u + 1}.inv
  have := DiagramLimitTransport.restriction_trivial
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram (basedPathProjection Y) (fromPoint Y))) i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso CospanShape.strictCospanHornIso.symm)
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone_isLimit _ _
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram (basedPathProjection Y) (fromPoint Y))) i)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (DiagramLimitTransport.restrict d i) :=
    (e.isTerminalVertex_iff d).1 hd
  exact hc.cast (CospanShape.strictDiagram_eq (basedPathProjection Y) (fromPoint Y))

end SerrePositivity.KST.Spectra.OmegaSpectrum.BasedLoop
