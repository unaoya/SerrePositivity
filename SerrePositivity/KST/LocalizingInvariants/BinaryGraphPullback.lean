module

public import SerrePositivity.KST.LocalizingInvariants.BinaryGraphSquare

/-!
概要：元の BF graph と対角の正方形は実 pullback である。
方針：第二射影を右へ貼り、上下の合成が恒等となる外周から右を消去する。
規約：graph の選んだ二次の可換性を保持。使われ方：元の二脚の極限錐への変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.BinaryGraph
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Y Z : OmegaSpectrum.{u}} (g : Y ⟶ Z)

lemma rectangle_outer_bottom :
    (squareBottomArrow (pastingSquare (rectangle g).diagram 1)).edge =
      (Truncated.Edge.id (X := (truncation 2).obj Sp.{u}) (coherentNerveVertex Y)).edge := by
  rw [squareBottomArrow_edge, pastingSquare_bottomEdge, (rectangle g).bottom_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  exact (SSet.yonedaEquiv.apply_symm_apply _).trans
    ((bottomComposition g).d₁.trans (congrArg SSet.Edge.edge (coherentNerveEdge_id Y)))

lemma rectangle_outer_top :
    (squareTopArrow (pastingSquare (rectangle g).diagram 1)).edge =
      (Truncated.Edge.id (X := (truncation 2).obj Sp.{u}) (coherentNerveVertex Z)).edge := by
  rw [squareTopArrow_edge, pastingSquare_topEdge, (rectangle g).top_eq,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  exact (SSet.yonedaEquiv.apply_symm_apply _).trans
    ((topComposition Z).d₁.trans (congrArg SSet.Edge.edge (coherentNerveEdge_id Z)))

lemma rectangle_outer_isPullback : IsPullbackSquare (pastingSquare (rectangle g).diagram 1) := by
  apply isPullbackSquare_of_horizontal_invertible
  · apply (isInvertibleEdge_congr (rectangle_outer_bottom g)).mpr
    change IsIso (Truncated.HomotopyCategory.homMk _)
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  · apply (isInvertibleEdge_congr (rectangle_outer_top g)).mpr
    change IsIso (Truncated.HomotopyCategory.homMk _)
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance

lemma square_isPullback : IsPullbackSquare (square g) := by
  have hr : IsPullbackSquare (pastingSquare (rectangle g).diagram 0) := by
    rw [(rectangle g).right_eq]
    exact BinarySecondProjection.square_isPullback g Z
  have hl := isPullbackSquare_pasting_cancel_right (rectangle g).diagram hr
    (rectangle_outer_isPullback g)
  rwa [(rectangle g).left_eq] at hl

end SerrePositivity.KST.LocalizingInvariants.BinaryGraph
