module

public import SerrePositivity.KST.LocalizingInvariants.BinaryProductCospanSquare
public import SerrePositivity.KST.LocalizingInvariants.BinaryGraphLeftClass
public import SerrePositivity.KST.LocalizingInvariants.SquareLeftNormalization

/-!
概要：積・対角の指定極限から、四辺を元の BF 射に固定した二脚の実 pullback を得る。
方針：graph の第二射影で未知の左脚の類を同定し、本体を保つ境界変形で元の b へ戻す。
規約：頂点は元の T。使われ方：d8 の元の E(A) を頂点とする極限錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.BinaryProductCospanNormalized
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {T X Y Z : OmegaSpectrum.{u}} (a : T ⟶ X) (b : T ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
  (hc : SpectrumHo.hom a ≫ SpectrumHo.hom f = SpectrumHo.hom b ≫ SpectrumHo.hom g)
  (S : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u}) (hS : IsPullbackSquare S)
  (ht : squareTopEdge ≫ S = SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.map f g)).edge)
  (hr : squareRightEdge ≫ S =
    SSet.yonedaEquiv.symm (coherentNerveEdge (BinaryGraph.diagonal Z)).edge)
  (hl : squareLeftEdge ≫ S =
    SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.lift a b)).edge)

lemma left_class : Truncated.HomotopyCategory.homMk
    (NativeSquareRows.left a g (BinaryProductCospan.square a b f g hc S hS ht hr hl)
      (BinaryProductCospan.square_bottom a b f g hc S hS ht hr hl)
      (BinaryProductCospan.square_top a b f g hc S hS ht hr hl)).toTruncated =
        SpectrumHo.hom b := by
  have hfront := BinaryGraph.left_class a b f g
    (BinaryProductDiagonal.square a b f g hc S hS ht hr)
    (BinaryProductDiagonal.square_bottom a b f g hc S hS ht hr hl)
    (BinaryProductDiagonal.square_top a b f g hc S hS ht hr)
    (BinaryProductDiagonal.square_right a b f g hc S hS ht hr)
  have he : (NativeSquareRows.left a g (BinaryProductCospan.square a b f g hc S hS ht hr hl)
      (BinaryProductCospan.square_bottom a b f g hc S hS ht hr hl)
      (BinaryProductCospan.square_top a b f g hc S hS ht hr hl)).toTruncated =
      (NativeSquareRows.left (Binary.lift a b) (BinaryGraph.graph g)
        (BinaryProductDiagonal.square a b f g hc S hS ht hr)
        (BinaryProductDiagonal.square_bottom a b f g hc S hS ht hr hl)
        (BinaryProductDiagonal.square_top a b f g hc S hS ht hr)).toTruncated := by
    apply Truncated.Edge.ext
    change (squareLeftArrow (BinaryProductCospan.square a b f g hc S hS ht hr hl)).edge =
      (squareLeftArrow (BinaryProductDiagonal.square a b f g hc S hS ht hr)).edge
    rw [squareLeftArrow_edge, squareLeftArrow_edge]
    apply congrArg SSet.yonedaEquiv
    change squareLeftEdge ≫ pastingSquare
      (BinaryProductCospan.rectangle a b f g hc S hS ht hr hl).diagram 1 = _
    rw [pastingSquare_outer_leftEdge,
      (BinaryProductCospan.rectangle a b f g hc S hS ht hr hl).left_eq]
  exact (congrArg Truncated.HomotopyCategory.homMk he).trans hfront

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  SquareLeftNormalization.square a b f g (BinaryProductCospan.square a b f g hc S hS ht hr hl)
    (BinaryProductCospan.square_bottom a b f g hc S hS ht hr hl)
    (BinaryProductCospan.square_top a b f g hc S hS ht hr hl)
    (BinaryProductCospan.square_right a b f g hc S hS ht hr hl)
    (left_class a b f g hc S hS ht hr hl)

lemma square_isPullback : IsPullbackSquare (square a b f g hc S hS ht hr hl) :=
  SquareLeftNormalization.square_isPullback _ _ _ _ _ _ _ _ _
    (BinaryProductCospan.square_isPullback a b f g hc S hS ht hr hl)

lemma square_bottom : squareBottomEdge ≫ square a b f g hc S hS ht hr hl =
    SSet.yonedaEquiv.symm (coherentNerveEdge a).edge :=
  SquareLeftNormalization.square_bottom _ _ _ _ _ _ _ _ _

lemma square_top : squareTopEdge ≫ square a b f g hc S hS ht hr hl =
    SSet.yonedaEquiv.symm (coherentNerveEdge g).edge :=
  SquareLeftNormalization.square_top _ _ _ _ _ _ _ _ _

lemma square_left : squareLeftEdge ≫ square a b f g hc S hS ht hr hl =
    SSet.yonedaEquiv.symm (coherentNerveEdge b).edge :=
  SquareLeftNormalization.square_left _ _ _ _ _ _ _ _ _

lemma square_right : squareRightEdge ≫ square a b f g hc S hS ht hr hl =
    SSet.yonedaEquiv.symm (coherentNerveEdge f).edge :=
  SquareLeftNormalization.square_right _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.BinaryProductCospanNormalized
