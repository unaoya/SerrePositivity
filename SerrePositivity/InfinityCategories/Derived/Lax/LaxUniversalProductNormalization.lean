module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFramePathExtension
public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductInclusion
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameEdgesHomotopy
public import SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy
public import SerrePositivity.KST.LocalizingInvariants.SquareFramePathExtension

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization
end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization
local instance instSimplicialCategoryOmegaSpectrum : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def bottomEdge : Sp.{u}.Edge (coherentNerveVertex (value Φ A))
    (coherentNerveVertex (Binary.obj (value Φ C) (value Φ D))) :=
  (SSet.Edge.ofTruncated (squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h))).ofEq
    (LaxUniversalProduct.vertex00 hΦ p q i r h) (LaxUniversalProduct.vertex10 hΦ p q i r h)

def topEdge : Sp.{u}.Edge (coherentNerveVertex (value Φ Q))
    (coherentNerveVertex (Binary.obj (value Φ Q) (value Φ Q))) :=
  (SSet.Edge.ofTruncated (squareTopArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h))).ofEq
    (LaxUniversalProduct.vertex01 hΦ p q i r h) (LaxUniversalProduct.vertex11 hΦ p q i r h)

def leftEdge : Sp.{u}.Edge (coherentNerveVertex (value Φ A)) (coherentNerveVertex (value Φ Q)) :=
  (SSet.Edge.ofTruncated (squareLeftArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h))).ofEq
    (LaxUniversalProduct.vertex00 hΦ p q i r h) (LaxUniversalProduct.vertex01 hΦ p q i r h)

def rightEdge : Sp.{u}.Edge (coherentNerveVertex (Binary.obj (value Φ C) (value Φ D)))
    (coherentNerveVertex (Binary.obj (value Φ Q) (value Φ Q))) :=
  (SSet.Edge.ofTruncated (squareRightArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h))).ofEq
    (LaxUniversalProduct.vertex10 hΦ p q i r h) (LaxUniversalProduct.vertex11 hΦ p q i r h)

def oldFrame : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame Sp.{u} := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.squareFrameOfEdges (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.bottomEdge hΦ p q i r h)
  (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.topEdge hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.leftEdge hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.rightEdge hΦ p q i r h)

lemma oldFrame_eq : _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.oldFrame hΦ p q i r h =
    _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h) := by
  apply _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.ext
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

lemma bottom_class : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.bottomEdge hΦ p q i r h).toTruncated =
    SpectrumHo.hom (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.bottomEdge hΦ p q i r h).toTruncated
    (squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h)) rfl).trans
      (LaxUniversalProduct.bottom_native_arrow hΦ p q i r h)

lemma top_class : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.topEdge hΦ p q i r h).toTruncated =
    SpectrumHo.hom (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q))) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.topEdge hΦ p q i r h).toTruncated
    (squareTopArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h)) rfl).trans
      (LaxUniversalProduct.top_arrow hΦ p q i r h)

lemma left_class : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.leftEdge hΦ p q i r h).toTruncated =
    SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap p q i r)) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.leftEdge hΦ p q i r h).toTruncated
    (squareLeftArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h)) rfl).trans
      (LaxUniversalProduct.left_arrow hΦ p q i r h)

lemma right_class : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.rightEdge hΦ p q i r h).toTruncated =
    SpectrumHo.hom (LaxUniversalProduct.legMap (Φ := Φ) p q r) := by
  apply hom_eq_of_arrow_mk_eq
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.rightEdge hΦ p q i r h).toTruncated
    (squareRightArrow (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h)) rfl).trans
      (LaxUniversalProduct.right_arrow hΦ p q i r h)

def newFrame : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame Sp.{u} := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.squareFrameOfEdges
  (coherentNerveEdge (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i))
  (coherentNerveEdge (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q))))
  (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap p q i r)))
  (coherentNerveEdge (LaxUniversalProduct.legMap (Φ := Φ) p q r))

def boundaryHomotopy : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.oldFrame hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.newFrame (Φ := Φ) p q i r) :=
  _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.squareFrameEdgesHomotopy (X := Sp.{u})
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.bottomEdge hΦ p q i r h)
    (coherentNerveEdge (IsLocalizingInvariant.laxQuotientProductInclusion (Φ := Φ) p q i))
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.topEdge hΦ p q i r h) (coherentNerveEdge (Binary.lift (𝟙 (value Φ Q)) (𝟙 (value Φ Q))))
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.leftEdge hΦ p q i r h)
    (coherentNerveEdge (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap p q i r)))
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.rightEdge hΦ p q i r h) (coherentNerveEdge (LaxUniversalProduct.legMap (Φ := Φ) p q r))
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.bottom_class hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.top_class hΦ p q i r h)
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.left_class hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.right_class hΦ p q i r h)

def extension : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.pathFrame (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.boundaryHomotopy hΦ p q i r h))
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.extension (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.boundaryHomotopy hΦ p q i r h)) _ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.oldFrame_eq hΦ p q i r h)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.extension hΦ p q i r h).target

def comparison : FunctorIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.comparison (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.extension hΦ p q i r h))

lemma square_boundary : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h =
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.newFrame (Φ := Φ) p q i r).diagram :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.extension_target_boundary (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.boundaryHomotopy hΦ p q i r h)) _ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.oldFrame_eq hΦ p q i r h)

lemma square_isPullback : IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square hΦ p q i r h) :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square_isPullback hΦ p q i r h).of_functorIso
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.comparison hΦ p q i r h)

end SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.bottomEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.bottomEdge := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.bottomEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.bottom_class := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.bottom_class

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.boundaryHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.boundaryHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.boundaryHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.comparison := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.comparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.extension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.extension := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.extension

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.instSimplicialCategoryOmegaSpectrum (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.instSimplicialCategoryOmegaSpectrum := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.instSimplicialCategoryOmegaSpectrum

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.leftEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.leftEdge := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.leftEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.left_class := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.left_class

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.newFrame (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.newFrame := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.newFrame

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.oldFrame (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.oldFrame := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.oldFrame

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.oldFrame_eq := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.oldFrame_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.rightEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.rightEdge := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.rightEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.right_class := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.right_class

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.square := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.square_boundary := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.square_isPullback := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.square_isPullback

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.topEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.topEdge := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.topEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.top_class := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.top_class

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProductNormalization.bottomEdge._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProductNormalization.bottomEdge._proof_1
