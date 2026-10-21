module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductInclusion
public import SerrePositivity.KST.LocalizingInvariants.SquareFrameEdgesHomotopy

/-!
概要：実積 pullback 正方形の四辺を、元の BF 包含の組・対角・核の射・積射に固定する。
方針：全図式から得た各辺の類を、同じ端点を固定した境界変形で元の BF 射へ移す。
規約：同じ E(A) と全図式の同型を保持。使われ方：対角 pullback と二脚 pullback の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def bottomEdge : Sp.{u}.Edge (coherentNerveVertex (value Φ A))
    (coherentNerveVertex (Binary.obj (value Φ C) (value Φ D))) :=
  (SSet.Edge.ofTruncated (squareBottomArrow (LaxUniversalProduct.square hΦ p q i r h))).ofEq
    (LaxUniversalProduct.vertex00 hΦ p q i r h) (LaxUniversalProduct.vertex10 hΦ p q i r h)

def topEdge : Sp.{u}.Edge (coherentNerveVertex (value Φ Q))
    (coherentNerveVertex (Binary.obj (value Φ Q) (value Φ Q))) :=
  (SSet.Edge.ofTruncated (squareTopArrow (LaxUniversalProduct.square hΦ p q i r h))).ofEq
    (LaxUniversalProduct.vertex01 hΦ p q i r h) (LaxUniversalProduct.vertex11 hΦ p q i r h)

def leftEdge : Sp.{u}.Edge (coherentNerveVertex (value Φ A)) (coherentNerveVertex (value Φ Q)) :=
  (SSet.Edge.ofTruncated (squareLeftArrow (LaxUniversalProduct.square hΦ p q i r h))).ofEq
    (LaxUniversalProduct.vertex00 hΦ p q i r h) (LaxUniversalProduct.vertex01 hΦ p q i r h)

def rightEdge : Sp.{u}.Edge (coherentNerveVertex (Binary.obj (value Φ C) (value Φ D)))
    (coherentNerveVertex (Binary.obj (value Φ Q) (value Φ Q))) :=
  (SSet.Edge.ofTruncated (squareRightArrow (LaxUniversalProduct.square hΦ p q i r h))).ofEq
    (LaxUniversalProduct.vertex10 hΦ p q i r h) (LaxUniversalProduct.vertex11 hΦ p q i r h)

def oldFrame : SquareFrame Sp.{u} := squareFrameOfEdges (bottomEdge hΦ p q i r h)
  (topEdge hΦ p q i r h) (leftEdge hΦ p q i r h) (rightEdge hΦ p q i r h)

lemma oldFrame_eq : oldFrame hΦ p q i r h =
    SquareFrame.ofSquare (LaxUniversalProduct.square hΦ p q i r h) := by
  apply SquareFrame.ext
  · change SSet.yonedaEquiv.symm (squareBottomArrow _).edge = _
    rw [squareBottomArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · change SSet.yonedaEquiv.symm (squareTopArrow _).edge = _
    rw [squareTopArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · change SSet.yonedaEquiv.symm (squareLeftArrow _).edge = _
    rw [squareLeftArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · change SSet.yonedaEquiv.symm (squareRightArrow _).edge = _
    rw [squareRightArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _

lemma bottom_class : Truncated.HomotopyCategory.homMk (bottomEdge hΦ p q i r h).toTruncated =
    SpectrumHo.hom (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (bottomEdge hΦ p q i r h).toTruncated
    (squareBottomArrow (LaxUniversalProduct.square hΦ p q i r h)) rfl).trans
      (LaxUniversalProduct.bottom_native_arrow hΦ p q i r h)

lemma top_class : Truncated.HomotopyCategory.homMk (topEdge hΦ p q i r h).toTruncated =
    SpectrumHo.hom (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q))) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (topEdge hΦ p q i r h).toTruncated
    (squareTopArrow (LaxUniversalProduct.square hΦ p q i r h)) rfl).trans
      (LaxUniversalProduct.top_arrow hΦ p q i r h)

lemma left_class : Truncated.HomotopyCategory.homMk (leftEdge hΦ p q i r h).toTruncated =
    SpectrumHo.hom (valueMap Φ (LaxUniversalDifference.kernelMap p q i r)) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (leftEdge hΦ p q i r h).toTruncated
    (squareLeftArrow (LaxUniversalProduct.square hΦ p q i r h)) rfl).trans
      (LaxUniversalProduct.left_arrow hΦ p q i r h)

lemma right_class : Truncated.HomotopyCategory.homMk (rightEdge hΦ p q i r h).toTruncated =
    SpectrumHo.hom (LaxUniversalProduct.legMap (Φ := Φ) p q r) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (rightEdge hΦ p q i r h).toTruncated
    (squareRightArrow (LaxUniversalProduct.square hΦ p q i r h)) rfl).trans
      (LaxUniversalProduct.right_arrow hΦ p q i r h)

def newFrame : SquareFrame Sp.{u} := squareFrameOfEdges
  (coherentNerveEdge (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i))
  (coherentNerveEdge (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q))))
  (coherentNerveEdge (valueMap Φ (LaxUniversalDifference.kernelMap p q i r)))
  (coherentNerveEdge (LaxUniversalProduct.legMap (Φ := Φ) p q r))

def boundaryHomotopy : SquareFrameHomotopy (oldFrame hΦ p q i r h) (newFrame (Φ := Φ) p q i r) :=
  squareFrameEdgesHomotopy (X := Sp.{u})
    (bottomEdge hΦ p q i r h)
    (coherentNerveEdge (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i))
    (topEdge hΦ p q i r h) (coherentNerveEdge (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q))))
    (leftEdge hΦ p q i r h)
    (coherentNerveEdge (valueMap Φ (LaxUniversalDifference.kernelMap p q i r)))
    (rightEdge hΦ p q i r h) (coherentNerveEdge (LaxUniversalProduct.legMap (Φ := Φ) p q r))
    (bottom_class hΦ p q i r h) (top_class hΦ p q i r h)
    (left_class hΦ p q i r h) (right_class hΦ p q i r h)

def extension : SquareFrame.PathExtension (boundaryHomotopy hΦ p q i r h).pathFrame
    (LaxUniversalProduct.square hΦ p q i r h) :=
  (boundaryHomotopy hΦ p q i r h).extension _ (oldFrame_eq hΦ p q i r h)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (extension hΦ p q i r h).target

def comparison : FunctorIso (LaxUniversalProduct.square hΦ p q i r h) (square hΦ p q i r h) :=
  (extension hΦ p q i r h).comparison

lemma square_boundary : SquareFrame.boundaryι ≫ square hΦ p q i r h =
    (newFrame (Φ := Φ) p q i r).diagram :=
  (boundaryHomotopy hΦ p q i r h).extension_target_boundary _ (oldFrame_eq hΦ p q i r h)

lemma square_isPullback : IsPullbackSquare (square hΦ p q i r h) :=
  (LaxUniversalProduct.square_isPullback hΦ p q i r h).of_functorIso
    (comparison hΦ p q i r h)

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization
