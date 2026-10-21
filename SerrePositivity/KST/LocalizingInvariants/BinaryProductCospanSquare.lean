module

public import SerrePositivity.KST.LocalizingInvariants.BinaryProductDiagonalFactorization

/-!
概要：積と対角の指定 pullback から、元の二脚の実 pullback を構成する。
方針：graph 付きの左 pullback に第一射影の基底変換を貼る。
規約：元の a・f・g を三辺に保持。使われ方：残る包含 b の辺の正規化と d8 の極限錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.BinaryProductCospan
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {T X Y Z : OmegaSpectrum.{u}} (a : T ⟶ X) (b : T ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
  (hc : SpectrumHo.hom a ≫ SpectrumHo.hom f = SpectrumHo.hom b ≫ SpectrumHo.hom g)
  (S : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u}) (hS : IsPullbackSquare S)
  (ht : squareTopEdge ≫ S = SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.map f g)).edge)
  (hr : squareRightEdge ≫ S =
    SSet.yonedaEquiv.symm (coherentNerveEdge (BinaryGraph.diagonal Z)).edge)
  (hl : squareLeftEdge ≫ S =
    SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.lift a b)).edge)

def bottomComposition : SSet.Edge.CompStruct (coherentNerveEdge (Binary.lift a b))
    (coherentNerveEdge (Binary.fst X Y)) (coherentNerveEdge a) :=
  (coherentNerveCompStruct (Binary.lift a b) (Binary.fst X Y)).ofEq rfl rfl
    (by rw [Binary.lift_fst])

def topComposition : SSet.Edge.CompStruct (coherentNerveEdge (BinaryGraph.graph g))
    (coherentNerveEdge (Binary.fst Z Y)) (coherentNerveEdge g) :=
  (coherentNerveCompStruct (BinaryGraph.graph g) (Binary.fst Z Y)).ofEq rfl rfl
    (by rw [BinaryGraph.graph, Binary.lift_fst])

def rectangle : SquarePastingRectangle
    (BinaryProductDiagonal.square a b f g hc S hS ht hr) (BinaryProjection.square f Y)
    (SSet.yonedaEquiv.symm (bottomComposition a b).simplex)
    (SSet.yonedaEquiv.symm (topComposition g).simplex) := by
  apply Classical.choice
  apply nonempty_squarePastingRectangle
  · rw [BinaryProductDiagonal.square_right, BinaryProjection.square_left]
  · rw [BinaryProductDiagonal.square_bottom a b f g hc S hS ht hr hl,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (bottomComposition a b).d₂.symm
  · rw [BinaryProjection.square_bottom, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (bottomComposition a b).d₀.symm
  · rw [BinaryProductDiagonal.square_top, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (topComposition g).d₂.symm
  · rw [BinaryProjection.square_top, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (topComposition g).d₀.symm

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  pastingSquare (rectangle a b f g hc S hS ht hr hl).diagram 1

lemma square_isPullback : IsPullbackSquare (square a b f g hc S hS ht hr hl) := by
  apply isPullbackSquare_pasting
  · rw [(rectangle a b f g hc S hS ht hr hl).left_eq]
    exact BinaryProductDiagonal.square_isPullback a b f g hc S hS ht hr
  · rw [(rectangle a b f g hc S hS ht hr hl).right_eq]
    exact BinaryProjection.square_isPullback f Y

lemma square_bottom : squareBottomEdge ≫ square a b f g hc S hS ht hr hl =
    SSet.yonedaEquiv.symm (coherentNerveEdge a).edge := by
  rw [square, pastingSquare_bottomEdge, (rectangle a b f g hc S hS ht hr hl).bottom_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (bottomComposition a b).d₁

lemma square_top : squareTopEdge ≫ square a b f g hc S hS ht hr hl =
    SSet.yonedaEquiv.symm (coherentNerveEdge g).edge := by
  rw [square, pastingSquare_topEdge, (rectangle a b f g hc S hS ht hr hl).top_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (topComposition g).d₁

lemma square_right : squareRightEdge ≫ square a b f g hc S hS ht hr hl =
    SSet.yonedaEquiv.symm (coherentNerveEdge f).edge := by
  rw [square, pastingSquare_outer_rightEdge, (rectangle a b f g hc S hS ht hr hl).right_eq,
    BinaryProjection.square_right]

end SerrePositivity.KST.LocalizingInvariants.BinaryProductCospan
