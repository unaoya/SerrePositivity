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
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance unitDiagramCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance unitDiagramNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)

def replacementUnitDiagramHomotopy := F2.prismHomotopy
  (F2.strictCoherentNatTransMap (CospanReplacement.unit p (fromPoint Y)))
  (F2.strictCoherentNatTransMap_zero _) (F2.strictCoherentNatTransMap_one _)

lemma replacementUnitDiagramHomotopy_vertical (x :
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} Limits.WalkingCospan))) _⦋0⦌) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge (replacementUnitDiagramHomotopy p) x).toTruncated := by
  have he := F2.prismHomotopy_vertical
    (F2.strictCoherentNatTransMap (CospanReplacement.unit p (fromPoint Y)))
    (F2.strictCoherentNatTransMap_zero _) (F2.strictCoherentNatTransMap_one _) x
  exact (isInvertibleEdge_congr (e :=
    (simplicialHomotopyVertexEdge (replacementUnitDiagramHomotopy p) x).toTruncated)
    (f := edgeOfSimplex _) he).mpr
      (F2.strictCoherentNatTransMap_vertical_isInvertible _
        (CospanReplacement.unit_isInvertible p (fromPoint Y)) x)

def replacementUnitDiagramIso := functorIsoOfPointwiseInvertibleHomotopy
  (replacementUnitDiagramHomotopy p) (replacementUnitDiagramHomotopy_vertical p)

lemma homotopyFiberConeTransportIso_base :
    Arrow.mk (homPre (joinInr Δ[0] _) (homotopyFiberConeTransportIso p).hom) =
      Arrow.mk (replacementUnitDiagramIso p).hom := by
  change Arrow.mk (homPre (joinInr Δ[0] _) (Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (homotopyFiberTransport p).homotopy))) = _
  unfold homPre
  rw [homMk_functorEdge_precomp]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change SSet.yonedaEquiv (MonoidalClosed.curry
    ((joinInr Δ[0] _ ▷ Δ[1]) ≫ (homotopyFiberTransport p).homotopy.h)) = _
  rw [(homotopyFiberTransport p).diagram]
  rfl

end SerrePositivity.KST.LocalizingInvariants.FiberModel
