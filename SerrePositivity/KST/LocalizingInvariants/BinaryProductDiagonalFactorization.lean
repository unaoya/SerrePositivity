module

public import SerrePositivity.KST.LocalizingInvariants.BinaryGraphPreliminaryRectangle
public import SerrePositivity.KST.LocalizingInvariants.PastingOuterLimitReplacement
public import SerrePositivity.KST.LocalizingInvariants.ReverseGridCospan

/-!
概要：積射と対角の指定 pullback を graph を右に持つ長方形へ厳密に延長する。
方針：予備長方形の外周 cospan を照合し、指定した極限正方形へ取り替える。
規約：外周と元の頂点は等号で保持。使われ方：元の二脚の pullback への変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.BinaryProductDiagonal
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {T X Y Z : OmegaSpectrum.{u}} (a : T ⟶ X) (b : T ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
  (hc : SpectrumHo.hom a ≫ SpectrumHo.hom f = SpectrumHo.hom b ≫ SpectrumHo.hom g)
  (S : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u}) (hS : IsPullbackSquare S)
  (ht : squareTopEdge ≫ S = SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.map f g)).edge)
  (hr : squareRightEdge ≫ S =
    SSet.yonedaEquiv.symm (coherentNerveEdge (BinaryGraph.diagonal Z)).edge)

include ht hr in
lemma preliminary_cospan :
    pullbackCospan (pastingSquare (BinaryGraphPreliminary.rectangle a b f g hc).diagram 1) =
      pullbackCospan S := by
  apply horn₂₂.isPushout.hom_ext
  · simp only [pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge]
    exact (BinaryGraphPreliminary.rectangle_outer_right a b f g hc).trans hr.symm
  · simp only [pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge]
    exact (BinaryGraphPreliminary.rectangle_outer_top a b f g hc).trans ht.symm

def replacement : PastingOuterLimitReplacement
    (BinaryGraphPreliminary.rectangle a b f g hc).diagram S :=
  pastingOuterLimitReplacement _ (BinaryGraphPreliminary.rectangle_right_isPullback a b f g hc)
    S hS (pushoutSpan_reverseGrid_eq_of_cospan_eq (preliminary_cospan a b f g hc S ht hr))

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    pastingSquare (replacement a b f g hc S hS ht hr).diagram 2

lemma square_isPullback : IsPullbackSquare (square a b f g hc S hS ht hr) :=
  (isPullbackSquare_iff_transpose _).1 (replacement a b f g hc S hS ht hr).left_isPullback

lemma square_bottom
    (hl : squareLeftEdge ≫ S =
      SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.lift a b)).edge) :
    squareBottomEdge ≫ square a b f g hc S hS ht hr =
      SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.lift a b)).edge := by
  rw [square, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_bottom, ← pastingSquare_outer_leftEdge,
    (replacement a b f g hc S hS ht hr).outer_eq]
  exact hl

lemma square_top : squareTopEdge ≫ square a b f g hc S hS ht hr =
    SSet.yonedaEquiv.symm (coherentNerveEdge (BinaryGraph.graph g)).edge := by
  rw [square, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_top, pastingSquare_sharedEdge,
    (replacement a b f g hc S hS ht hr).right_eq,
    (BinaryGraphPreliminary.rectangle a b f g hc).right_eq,
    _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_left, BinaryGraph.square_bottom]

lemma square_right : squareRightEdge ≫ square a b f g hc S hS ht hr =
    SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.map f (𝟙 Y))).edge := by
  rw [square, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.square_transpose_right, pastingSquare_topEdge,
    (replacement a b f g hc S hS ht hr).top_eq,
    (BinaryGraphPreliminary.rectangle a b f g hc).top_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (BinaryGraphPreliminary.productComposition f g).d₂

end SerrePositivity.KST.LocalizingInvariants.BinaryProductDiagonal
