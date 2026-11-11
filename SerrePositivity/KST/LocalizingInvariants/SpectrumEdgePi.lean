module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyFunctor
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquareArrows

/-!
概要：任意の Sp の辺に対する π 関手の作用を、元の BF 射の整数 π と照合する。
方針：端点を復号した辺の類を、端点等号の同型で正規化した元の類に一致させる。
規約：辺の一次単体を保持する。使われ方：局所化不変量の元の射への長完全列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

local instance edgePiSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {x y : Sp.{u} _⦋0⦌} (e : Sp.{u}.Edge x y)

/-- 元の両端を BF 対象へ復号し、同じ一単体を BF 射として読む。 -/
def edgeMap : spectrum (SSet.HomotopyCategory.mk x) ⟶
    spectrum (SSet.HomotopyCategory.mk y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (e.ofEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object y).symm)

lemma edgeMap_edge : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (edgeMap e)).edge = e.edge :=
  congrArg SSet.Edge.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom (e.ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object y).symm))

lemma edgeMap_hom : hom (edgeMap e) =
    normalize (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) := by
  have h := FiberModel.homMk_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (edgeMap e)).toTruncated
    e.toTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object y) (edgeMap_edge e)
  change hom (edgeMap e) ≫ (spectrumIso (SSet.HomotopyCategory.mk y)).hom =
    (spectrumIso (SSet.HomotopyCategory.mk x)).hom ≫
      SSet.Truncated.HomotopyCategory.homMk e.toTruncated at h
  have hh := congrArg (fun m ↦ m ≫ (spectrumIso (SSet.HomotopyCategory.mk y)).inv) h
  simpa only [normalize, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    SSet.HomotopyCategory.mk] using hh

/-- 任意の元の辺への π の作用は、同じ辺を表す元の BF 射の作用に一致する。 -/
lemma piMap_edge (j : ℤ) :
    piMap (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) j =
      homotopyMap (edgeMap e) j := by
  apply homotopyMap_eq_of_hom_eq
  exact (hom_representative _).trans (edgeMap_hom e).symm

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
