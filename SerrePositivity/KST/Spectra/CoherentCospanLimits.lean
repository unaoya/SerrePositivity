module

public import SerrePositivity.KST.Spectra.CoherentCospanPresentation
public import SerrePositivity.KST.Spectra.SpectrumCospanReplacement

/-!
概要：Sp の任意の coherent cospan 上の実際の ∞ 極限錐を構成する。
方針：二辺を BF 射へ復元し、fibration 置換した通常の cospan の極限錐を形状同型で移す。
規約：coherent 図式は任意で、厳密な図式から来るという仮定を要求しない。
使われ方：HTT 4.2.4.1、HA §1.4.2。Sp の fiber と有限極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CoherentPullback
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 任意の coherent cospan は実際の Sp 内で極限を持つ。 -/
lemma exists_limitCone (p : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u}) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  obtain ⟨E, X, B, f, g, h⟩ := CospanShape.exists_presentation p
  let d := CospanReplacement.infinityCone f g
  let i := CospanShape.strictCospanHornIso.{u, u + 1}.inv
  have := DiagramLimitTransport.restriction_trivial
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f g)) i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso CospanShape.strictCospanHornIso.symm)
  let c := DiagramLimitTransport.restrict d i
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f g)) i)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c :=
    (e.isTerminalVertex_iff d).1 (CospanReplacement.infinityCone_isLimit f g)
  exact ⟨c.cast h, hc.cast h⟩

/-- 任意の元の coherent 図式を底に持つ、選択した実際の極限錐。 -/
def infinityCone (p : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p :=
  (exists_limitCone p).choose

/-- 選択した錐は指定された coherent 図式の ∞ 極限である。 -/
lemma infinityCone_isLimit (p : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (infinityCone p) := (exists_limitCone p).choose_spec

/-- Sp の全ての coherent cospan に対する極限の存在界面。 -/
lemma hasLimit (p : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p :=
  ⟨infinityCone p, infinityCone_isLimit p⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum.CoherentPullback
