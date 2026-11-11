module

public import SerrePositivity.KST.Spectra.SpectrumReplacementEquivalences
public import SerrePositivity.KST.Spectra.StrictDiagramTransformation
public import SerrePositivity.KST.Spectra.DiagramLimitExistenceTransport
public import SerrePositivity.KST.Spectra.Limits.SpectrumHomFibrations

/-!
概要：任意のスペクトル cospan と、一脚 fibration に置換した cospan の実際の比較。
方針：既存の BF fibration 置換単位を左成分とし、残りを恒等にする。
規約：自然性は厳密な因子分解の等式。全成分は元の Sp の可逆な辺を与える。
使われ方：BF 1978 §2、HTT 4.2.4.1。任意の cospan の ∞ 引き戻し。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement
noncomputable section
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y
variable {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)

/-- 任意の元の cospan から、一脚 fibration の cospan への厳密な自然変換。 -/
def ordinaryUnit : cospan f g ⟶ cospan (fibrationReplacementProjection f) g :=
  cospanHomMk (𝟙 B) (fibrationReplacementUnit f) (𝟙 X)
    (by simp) (by simp)

/-- Hom の宇宙に持ち上げた、実際の二つの cospan 図式の比較。 -/
def unit : _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f g ⟶
    _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram (fibrationReplacementProjection f) g :=
  Functor.whiskerLeft AsSmall.down (ordinaryUnit f g)

/-- 左成分は既存の fibration 置換単位そのもの。 -/
lemma unit_left : (_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.unit f g).app (AsSmall.up.obj WalkingCospan.left) =
    fibrationReplacementUnit f := rfl

/-- 全ての成分は実際の Sp の同値。 -/
lemma unit_isInvertible (j : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.unit f g).app j)) := by
  rcases j with ⟨_ | (_ | _)⟩
  · exact SpectrumMappingAcyclic.isInvertible_of_levelwise (𝟙 B)
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _)
  · exact fibrationReplacementUnit_isInvertible f
  · exact SpectrumMappingAcyclic.isInvertible_of_levelwise (𝟙 X)
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _)

/-- 置換した図式には構成済みの実際の ∞ 極限錐がある。 -/
lemma replaced_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone (fibrationReplacementProjection f) g) :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone_isLimit _ _

/-- 置換単位が与える、元の cospan と置換した cospan の実際の図式同型。 -/
def diagramIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f g))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram (fibrationReplacementProjection f) g)) :=
  StrictDiagramTransformation.functorIso (_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.unit f g) (_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.unit_isInvertible f g)

/-- 任意の cospan の極限錐を、置換の homotopy pullback と同じ頂点で構成できる。 -/
lemma exists_limitCone :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f g)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex =
        (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone (fibrationReplacementProjection f) g).vertex :=
  DiagramLimitTransport.exists_limitCone_of_functorIso (_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.diagramIso f g)
    _ (_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.replaced_isLimit f g)

/-- 任意の元の cospan 上の実際の ∞ 極限錐。 -/
def infinityCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f g)) :=
  (_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.exists_limitCone f g).choose

/-- 構成した錐は元の図式の ∞ 極限である。 -/
lemma infinityCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.infinityCone f g) :=
  (_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.exists_limitCone f g).choose_spec.1

/-- 極限錐の頂点は具体的な BF homotopy pullback の頂点である。 -/
lemma infinityCone_vertex : (_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.infinityCone f g).vertex =
    (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone (fibrationReplacementProjection f) g).vertex :=
  (_root_.SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement.exists_limitCone f g).choose_spec.2

end
end SerrePositivity.KST.Spectra.OmegaSpectrum.CospanReplacement
