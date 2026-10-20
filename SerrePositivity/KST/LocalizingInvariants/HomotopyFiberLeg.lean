module

public import SerrePositivity.KST.LocalizingInvariants.ReplacedFiberLeg
public import SerrePositivity.InfinityCategories.F2.EdgeSquareTransport

/-!
概要：任意射の元の cospan 上の錐の脚と、元の homotopyFiberInclusion の類の一致。
方針：指定単位の prism の自然性と、単位の厳密な右逆による打ち消しを使う。
規約：置換後の包含だけに主張を弱めない。使われ方：K-5 の長完全列の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance homotopyFiberLegSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance homotopyFiberLegHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable {E B : OmegaSpectrum.{u}} (f : E ⟶ B)

/-- 元の図式上の錐の脚を、元の BF fiber を始域とする射へ戻す。 -/
def homotopyFiberLeg (i : AsSmall.{u} WalkingCospan) : homotopyFiber f ⟶
    (spectrumPullbackDiagram f (fromPoint B)).obj i :=
  SpectrumConeLeg.map (homotopyFiberCone f) (homotopyFiberCone_vertex f) i

lemma homotopyFiberTransport_apexEdge :
    (F2.coneHomotopyApexEdge (homotopyFiberTransport f).homotopy).edge =
      (coherentNerveEdge (𝟙 (homotopyFiber f))).edge := by
  have h := StrictConeTransport.apexEdge (CospanReplacement.unit f (fromPoint B))
    (CospanReplacement.unit_isInvertible f (fromPoint B))
    (replacedCone (fibrationReplacementProjection f))
    (replacedCone_isLimit (fibrationReplacementProjection f))
  change (F2.coneHomotopyApexEdge (homotopyFiberTransport f).homotopy).edge =
    PinchedHom.constant (replacedCone (fibrationReplacementProjection f)).vertex 1 at h
  have hv := congrArg (fun v : Sp.{u} _⦋0⦌ ↦ PinchedHom.constant v 1)
    (replacedCone_vertex (fibrationReplacementProjection f))
  exact h.trans (hv.trans (by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl))

lemma homotopyFiberTransport_diagramEdge (i : AsSmall.{u} WalkingCospan) :
    (F2.coneHomotopyDiagramEdge (homotopyFiberTransport f).homotopy
      (ULift.up (ComposableArrows.mk₀ i))).edge =
      (coherentNerveEdge ((CospanReplacement.unit f (fromPoint B)).app i)).edge :=
  StrictConeTransport.diagramEdge (CospanReplacement.unit f (fromPoint B))
    (CospanReplacement.unit_isInvertible f (fromPoint B))
    (replacedCone (fibrationReplacementProjection f))
    (replacedCone_isLimit (fibrationReplacementProjection f)) i

/-- 元の各脚を置換単位と合成すると、置換後の対応する脚の類になる。 -/
lemma homotopyFiberLeg_unit (i : AsSmall.{u} WalkingCospan) :
    SpectrumHo.hom (homotopyFiberLeg f i) ≫
        SpectrumHo.hom ((CospanReplacement.unit f (fromPoint B)).app i) =
      SpectrumHo.hom (replacedLeg (fibrationReplacementProjection f) i) := by
  let G := (homotopyFiberTransport f).homotopy
  let k := ULift.up (ComposableArrows.mk₀ i)
  have h := F2.coneHomotopy_leg_naturality G k
  have hs := F2.homMk_square_transport
    (F2.nativeConeLeg (homotopyFiberCone f) k) (F2.coneHomotopyDiagramEdge G k)
    (F2.coneHomotopyApexEdge G)
    (F2.nativeConeLeg (replacedCone (fibrationReplacementProjection f)) k)
    (coherentNerveEdge (homotopyFiberLeg f i)).toTruncated
    (coherentNerveEdge ((CospanReplacement.unit f (fromPoint B)).app i)).toTruncated
    (coherentNerveEdge (𝟙 (homotopyFiber f))).toTruncated
    (coherentNerveEdge (replacedLeg (fibrationReplacementProjection f) i)).toTruncated
    h (homotopyFiberCone_vertex f)
    (strictCoherentDiagram_vertex (spectrumPullbackDiagram f (fromPoint B)) i)
    (replacedCone_vertex (fibrationReplacementProjection f))
    (strictCoherentDiagram_vertex
      (spectrumPullbackDiagram (fibrationReplacementProjection f) (fromPoint B)) i)
    (SpectrumConeLeg.map_edge _ _ i).symm (homotopyFiberTransport_diagramEdge f i)
    (homotopyFiberTransport_apexEdge f) (SpectrumConeLeg.map_edge _ _ i).symm
  change SpectrumHo.hom (homotopyFiberLeg f i) ≫
      SpectrumHo.hom ((CospanReplacement.unit f (fromPoint B)).app i) =
    SpectrumHo.hom (𝟙 (homotopyFiber f)) ≫
      SpectrumHo.hom (replacedLeg (fibrationReplacementProjection f) i) at hs
  simpa only [SpectrumHo.hom_id, Category.id_comp] using hs

/-- 元の図式上の fiber への脚は、元の homotopyFiberInclusion の類そのもの。 -/
lemma homotopyFiberLeg_left_hom :
    SpectrumHo.hom (homotopyFiberLeg f (AsSmall.up.obj WalkingCospan.left)) =
      SpectrumHo.hom (homotopyFiberInclusion f) := by
  let l := homotopyFiberLeg f (AsSmall.up.obj WalkingCospan.left)
  let p := fibrationReplacementProjection f
  have h : SpectrumHo.hom l ≫ SpectrumHo.hom (fibrationReplacementUnit f) =
      SpectrumHo.hom (fiberInclusion p inferInstance) :=
    (homotopyFiberLeg_unit f (AsSmall.up.obj WalkingCospan.left)).trans (replacedLeg_left_hom p)
  calc
    SpectrumHo.hom l = SpectrumHo.hom l ≫
        (SpectrumHo.hom (fibrationReplacementUnit f) ≫
          SpectrumHo.hom (fibrationReplacementRetraction f)) := by
      rw [← SpectrumHo.hom_comp, fibrationReplacementUnit_retraction, SpectrumHo.hom_id,
        Category.comp_id]
    _ = (SpectrumHo.hom l ≫ SpectrumHo.hom (fibrationReplacementUnit f)) ≫
        SpectrumHo.hom (fibrationReplacementRetraction f) := (Category.assoc _ _ _).symm
    _ = SpectrumHo.hom (fiberInclusion p inferInstance) ≫
        SpectrumHo.hom (fibrationReplacementRetraction f) :=
      congrArg (fun z ↦ z ≫ SpectrumHo.hom (fibrationReplacementRetraction f)) h
    _ = SpectrumHo.hom (homotopyFiberInclusion f) := (SpectrumHo.hom_comp _ _).symm

end SerrePositivity.KST.LocalizingInvariants.FiberModel
