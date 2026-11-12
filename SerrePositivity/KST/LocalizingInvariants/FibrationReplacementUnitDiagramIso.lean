module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeTransportIso
public import SerrePositivity.KST.LocalizingInvariants.StrictConeHomotopyRestriction

/-!
概要：fibration 置換単位の元の全図式 prism 自体を、可逆な h Fun の射として保持する。
方針：prism の全頂点の可逆性を元のホモトピーへ移し、その同じ辺の類を同型にする。
規約：別の同型の存在で元の prism を置き換えない。使われ方：模型 cube の底の共役。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance unitDiagramCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance unitDiagramNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)

def replacementUnitDiagramHomotopy := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.prismHomotopy
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap (CospanReplacement.unit p (fromPoint Y)))
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_zero _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_one _)

lemma replacementUnitDiagramHomotopy_vertical (x :
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} Limits.WalkingCospan))) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (replacementUnitDiagramHomotopy p) x).toTruncated := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.prismHomotopy_vertical
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap (CospanReplacement.unit p (fromPoint Y)))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_zero _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_one _) x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (replacementUnitDiagramHomotopy p) x).toTruncated)
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex _) he).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap_vertical_isInvertible _
        (CospanReplacement.unit_isInvertible p (fromPoint Y)) x)

def replacementUnitDiagramIso := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy
  (replacementUnitDiagramHomotopy p) (replacementUnitDiagramHomotopy_vertical p)

lemma homotopyFiberConeTransportIso_base :
    Arrow.mk (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) (homotopyFiberConeTransportIso p).hom) =
      Arrow.mk (replacementUnitDiagramIso p).hom := by
  change Arrow.mk (homPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (homotopyFiberTransport p).homotopy))) = _
  unfold homPre
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change SSet.yonedaEquiv (MonoidalClosed.curry
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _ ▷ Δ[1]) ≫ (homotopyFiberTransport p).homotopy.h)) = _
  rw [(homotopyFiberTransport p).diagram]
  rfl

end SerrePositivity.KST.LocalizingInvariants.FiberModel
