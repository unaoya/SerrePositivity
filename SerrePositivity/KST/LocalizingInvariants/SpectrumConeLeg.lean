module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomClass
public import SerrePositivity.InfinityCategories.F2.CatInfinity.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv

/-!
概要：Sp の錐の脚を、元の端点を持つ BF 射として回収する。
方針：錐頂点と図式頂点の等号で端点を合わせ、coherent 辺と通常射の同値を使う。
規約：一単体自体を保持する。使われ方：K-5 の置換前後の包含の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumConeLeg

local instance spectrumLegSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {I : Type u} [SmallCategory I] {D : I ⥤ OmegaSpectrum.{u}}
  (c : JoinCone (strictCoherentDiagram D)) {Z : OmegaSpectrum.{u}}
  (hz : c.vertex = coherentNerveVertex Z) (i : I)

/-- 錐の元の脚の辺を指定された BF 対象間の辺として表示する。 -/
def edge : Sp.{u}.Edge (coherentNerveVertex Z) (coherentNerveVertex (D.obj i)) where
  edge := (F2.nativeConeLeg c (ULift.up (ComposableArrows.mk₀ i))).edge
  src_eq := (F2.nativeConeLeg c _).src_eq.trans hz
  tgt_eq := (F2.nativeConeLeg c _).tgt_eq.trans (strictCoherentDiagram_vertex D i)

def map : Z ⟶ D.obj i := coherentNerveEdgeToHom (edge c hz i)

lemma map_edge : (coherentNerveEdge (map c hz i)).edge =
    (F2.nativeConeLeg c (ULift.up (ComposableArrows.mk₀ i))).edge :=
  congrArg SSet.Edge.edge (coherentNerveEdge_hom (edge c hz i))

/-- 元の通常の錐なら、回収した射は元の脚そのもの。 -/
lemma map_strict (b : CategoryTheory.Limits.Cone D) :
    map (strictCoherentCone b) (strictCoherentCone_vertex b) i = b.π.app i := by
  have he : coherentNerveEdge (map (strictCoherentCone b) (strictCoherentCone_vertex b) i) =
      coherentNerveEdge (b.π.app i) := SSet.Edge.ext
    ((map_edge _ _ i).trans (F2.nativeConeLeg_strict b i))
  have h := congrArg (coherentNerveEdgeToHom (C := OmegaSpectrum.{u})) he
  simpa only [coherentNerveEdgeToHom_edge] using h

end SerrePositivity.KST.LocalizingInvariants.SpectrumConeLeg
