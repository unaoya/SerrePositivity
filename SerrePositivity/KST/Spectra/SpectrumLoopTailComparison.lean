module

public import SerrePositivity.KST.Spectra.SpectrumTailEnriched
public import SerrePositivity.KST.Spectra.SpectrumLoopEssentialSurjectivity
public import SerrePositivity.KST.Spectra.SpectrumLoopEquivalences

/-!
概要：Sp の実際の loop 関手と一段移動の両合成を対象ごとに比較する。
方針：円の置換比較を一段移動し、指定した loop 四角形との同型を関手で写す。
規約：対象ごとの同型であり、関手同型や完全忠実性は別に証明する。
使われ方：Sp の loop と一段移動が互いに逆であることの対象上の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance loopTailSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance loopTailHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- Kan 円と通常の円の cotensor の比較を一段移動した実際の BF 射。 -/
def circleReplacementTailComparison (X : OmegaSpectrum.{u}) :
    rationalizationModel X ⟶ tail (cotensor PointedSimplicialSet.circle X) :=
  tailMap (cotensorPre CirclePower.unit X)

/-- 円の置換比較を一段移動した辺も元の Sp の同値。 -/
lemma circleReplacementTailComparison_isInvertible (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circleReplacementTailComparison X)) := by
  apply SpectrumMappingAcyclic.isInvertible_of_levelwise
  intro n
  exact cotensorPre_levelwise_of_anodyne CirclePower.unit
    (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle) X (n + 1)

/-- 一段先の二つの円の cotensor の具体的な同型。 -/
def circleReplacementTailVertexIso (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (rationalizationModel X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (tail (cotensor PointedSimplicialSet.circle X))) := by
  haveI := circleReplacementTailComparison_isInvertible X
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circleReplacementTailComparison X)))

/-- loop の後で一段移動すると、対象ごとに元の頂点と同型。 -/
def nativeTailLoopVertexIso (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (nativeTail.app (Opposite.op ⦋0⦌) (nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
    (nativeLoopVertexIso (BasedLoop.square X) ≪≫ (BasedLoop.circleVertexIso X).symm) nativeTail
  rw [nativeTail_vertex] at h
  exact h ≪≫ (circleReplacementTailVertexIso X).symm ≪≫ (originalLoopModelVertexIso X).symm

/-- 元の Sp の一段移動関手も本質的全射。 -/
lemma nativeTail_essentiallySurjective : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective nativeTail.{u} := by
  intro x
  obtain ⟨X, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv OmegaSpectrum.{u}).surjective x
  exact ⟨nativeLoop.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X), ⟨nativeTailLoopVertexIso X⟩⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum
