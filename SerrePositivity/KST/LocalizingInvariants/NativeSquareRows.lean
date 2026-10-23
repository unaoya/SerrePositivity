module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomClass
public import SerrePositivity.InfinityCategories.F2.CatInfinity.EdgeSquareTransport
public import SerrePositivity.InfinityCategories.Stable.PastingSplitProjection

/-!
概要：元の BF 射を上下辺に持つ正方形の残る二辺を、同じ BF 頂点間の辺にする。
方針：一次単体から端点を照合し、元の正方形の可換性を同じ四頂点へ輸送する。
規約：端点の輸送を射の類にも明示する。使われ方：graph 正方形の未知の脚の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.NativeSquareRows
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {T X Y Z : OmegaSpectrum.{u}} (a : T ⟶ X) (g : Y ⟶ Z)
  (S : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u})
  (hb : squareBottomEdge ≫ S = SSet.yonedaEquiv.symm (coherentNerveEdge a).edge)
  (ht : squareTopEdge ≫ S = SSet.yonedaEquiv.symm (coherentNerveEdge g).edge)

include hb in
lemma bottom_raw : (squareBottomArrow S).edge = (coherentNerveEdge a).edge := by
  rw [squareBottomArrow_edge, hb]
  exact SSet.yonedaEquiv.apply_symm_apply _

include ht in
lemma top_raw : (squareTopArrow S).edge = (coherentNerveEdge g).edge := by
  rw [squareTopArrow_edge, ht]
  exact SSet.yonedaEquiv.apply_symm_apply _

include hb in
lemma vertex00 : squareVertex S 0 0 = coherentNerveVertex T :=
  (squareBottomArrow S).src_eq.symm.trans
    ((congrArg (Sp.{u}.δ 1) (bottom_raw a S hb)).trans (coherentNerveEdge a).src_eq)

include hb in
lemma vertex10 : squareVertex S 1 0 = coherentNerveVertex X :=
  (squareBottomArrow S).tgt_eq.symm.trans
    ((congrArg (Sp.{u}.δ 0) (bottom_raw a S hb)).trans (coherentNerveEdge a).tgt_eq)

include ht in
lemma vertex01 : squareVertex S 0 1 = coherentNerveVertex Y :=
  (squareTopArrow S).src_eq.symm.trans
    ((congrArg (Sp.{u}.δ 1) (top_raw g S ht)).trans (coherentNerveEdge g).src_eq)

include ht in
lemma vertex11 : squareVertex S 1 1 = coherentNerveVertex Z :=
  (squareTopArrow S).tgt_eq.symm.trans
    ((congrArg (Sp.{u}.δ 0) (top_raw g S ht)).trans (coherentNerveEdge g).tgt_eq)

def left : Sp.{u}.Edge (coherentNerveVertex T) (coherentNerveVertex Y) :=
  (SSet.Edge.ofTruncated (squareLeftArrow S)).ofEq (vertex00 a S hb) (vertex01 g S ht)

def right : Sp.{u}.Edge (coherentNerveVertex X) (coherentNerveVertex Z) :=
  (SSet.Edge.ofTruncated (squareRightArrow S)).ofEq (vertex10 a S hb) (vertex11 g S ht)

lemma comm : SpectrumHo.hom a ≫ Truncated.HomotopyCategory.homMk
    (right a g S hb ht).toTruncated =
      Truncated.HomotopyCategory.homMk (left a g S hb ht).toTruncated ≫ SpectrumHo.hom g :=
  F2.homMk_square_transport (squareBottomArrow S) (squareRightArrow S)
    (squareLeftArrow S) (squareTopArrow S) (coherentNerveEdge a).toTruncated
    (right a g S hb ht).toTruncated (left a g S hb ht).toTruncated
    (coherentNerveEdge g).toTruncated (square_homMk_comm S)
    (vertex00 a S hb) (vertex10 a S hb) (vertex01 g S ht) (vertex11 g S ht)
    (bottom_raw a S hb) rfl rfl (top_raw g S ht)

include hb ht in
lemma right_class (f : X ⟶ Z)
    (hr : squareRightEdge ≫ S = SSet.yonedaEquiv.symm (coherentNerveEdge f).edge) :
    Truncated.HomotopyCategory.homMk (right a g S hb ht).toTruncated = SpectrumHo.hom f := by
  apply congrArg Truncated.HomotopyCategory.homMk
  apply Truncated.Edge.ext
  change (squareRightArrow S).edge = _
  rw [squareRightArrow_edge, hr]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.KST.LocalizingInvariants.NativeSquareRows
