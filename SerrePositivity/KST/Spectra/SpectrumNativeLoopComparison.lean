module

public import SerrePositivity.KST.Spectra.EndpointLoopComparisonEquivalence
public import SerrePositivity.KST.Spectra.CotensorSourceIso

/-!
概要：通常の円による BF cotensor は元の Sp の native な loop 対象に同値。
方針：円の厳密な表示同型による制限と、path 引き戻しへの実際の比較を合成する。
規約：比較辺を指定し、その各段の全基点 π 同型と可逆性を証明する。
使われ方：HA §1.4.2、Sp の loop と添字移動および安定性の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.BasedLoop

/-- 通常の円の BF cotensor から具体的な native loop 対象への実際の射。 -/
def circleComparison (Y : OmegaSpectrum.{u}) :
    cotensor PointedSimplicialSet.circle.{u} Y ⟶ obj Y :=
  cotensorPre endpointCircleIso.{u}.hom Y ≫ comparison Y

/-- 通常の円の比較は各段で全基点 π 同型。 -/
lemma circleComparison_levelwise (Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((circleComparison Y).app n).right :=
  (cotensorPre_levelwise_of_isIso endpointCircleIso.hom Y n).comp (comparison_levelwise Y n)

local instance nativeLoopSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance nativeLoopHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 指定した通常の円の比較辺は元の Sp の同値。 -/
lemma circleComparison_isInvertible (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circleComparison Y)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (circleComparison_levelwise Y)

/-- 通常の円の BF cotensor と実際の loop 四角形の頂点の具体的な同型。 -/
def circleVertexIso (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle.{u} Y))
      (square Y).vertex := by
  rw [square_vertex]
  haveI := circleComparison_isInvertible Y
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circleComparison Y)))

end SerrePositivity.KST.Spectra.OmegaSpectrum.BasedLoop
