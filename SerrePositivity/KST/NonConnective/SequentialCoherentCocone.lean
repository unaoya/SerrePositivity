module

public import SerrePositivity.KST.NonConnective.SequentialCoherentLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralHomHolimComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictNativeCocones
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColimitExistenceTransfer

/-!
概要：元の逐次 BF 図式上の実際の coherent Sp 余錐。
方針：反変 Hom end の整合した持ち上げを反対圏の錐へ送り、元の添字と Sp へ戻す。
規約：頂点は filteredOmegaSpectrum そのもの。∞ 余極限性は別に証明する。
使われ方：K-7 工程 1。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance sequentialCoconeSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance sequentialCoconeOppositeHomKan (X Y : OmegaSpectrum.{u}ᵒᵖ) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex Y.unop X.unop

/-- BF 標的の Raw Hom 図式を、反対の単体的圏の元の Hom 図式と比較する。 -/
def sequentialBFHomDiagramIso (D : SpectrumSequence.{u}) :
    sequentialRawHomDiagram D (sequentialSpectrum D).toKanSequence ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D.op (Opposite.op (sequentialSpectrum D)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {i j} f ↦ by
    change RawSpectrumMapping.pre (D.map f.unop) (sequentialSpectrum D).toKanSequence ≫ 𝟙 _ =
      𝟙 _ ≫ eHomWhiskerRight SSet (D.map f.unop) (sequentialSpectrum D)
    rw [Category.comp_id, Category.id_comp]
    exact RawSpectrumMapping.pre_spectrum (D.map f.unop) (sequentialSpectrum D))

/-- 元の反対図式と BF 候補を固定した coherent 錐の切断点。 -/
def sequentialCoherentOppositeConePoint (D : SpectrumSequence.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D.op)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op (sequentialSpectrum D)))) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison D.op (Opposite.op (sequentialSpectrum D))).app _
    (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight SequentialIndexᵒᵖ)
      (Functor.whiskerRight (sequentialBFHomDiagramIso D).hom SSet.opFunctor)).app _
        (sequentialReflectedBFInjectionPoint D)))

/-- 全高次の整合を持つ、元の反対の BF 図式上の実錐。 -/
def sequentialCoherentOppositeCone (D : SpectrumSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D.op) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D.op)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op (sequentialSpectrum D)))).symm
      (sequentialCoherentOppositeConePoint D)).val

/-- 実反対錐の頂点は、元の BF 候補の反対対象。 -/
lemma sequentialCoherentOppositeCone_vertex (D : SpectrumSequence.{u}) :
    (sequentialCoherentOppositeCone D).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op (sequentialSpectrum D)) := by
  have h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D.op)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op (sequentialSpectrum D)))).symm
      (sequentialCoherentOppositeConePoint D)).property
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  exact (congrArg SSet.yonedaEquiv h).trans (Equiv.apply_symm_apply _ _)

/-- 元の逐次 BF 図式を厳密に底に持つ実 Sp 余錐。 -/
def sequentialCoherentCocone (D : SpectrumSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoherentCoconeDiagram_eq D)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconePost ((sequentialCoherentOppositeCone D).reverseCocone.restrict
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeIndexIso.{u, u + 1} SequentialIndex).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentOppositeReturnIso OmegaSpectrum.{u}).hom)

/-- 元の Sp 余錐の頂点は、既存の filtered BF 置換そのもの。 -/
lemma sequentialCoherentCocone_vertex (D : SpectrumSequence.{u}) :
    (sequentialCoherentCocone D).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (sequentialSpectrum D) := by
  rw [sequentialCoherentCocone, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconePost_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.reverseCocone_vertex,
    sequentialCoherentOppositeCone_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentOppositeReturnIso_hom_vertex _

end SerrePositivity.KST.NonConnective
