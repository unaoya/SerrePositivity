module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalValueVertices
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport

/-!
概要：普遍差の元の比較正方形の四辺は、元の包含・対角・核の射・J の値である。
方針：全正方形の四辺の厳密等式から、端点輸送を含む h Sp の Arrow 等号へ移す。
規約：任意の可換四辺を選び直さない。使われ方：実積への輸送後の辺の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalValue
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable (Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u})
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

lemma bottom_arrow : Arrow.mk (squareHoBottom (square Φ p q i r h)) =
    Arrow.mk (SpectrumHo.hom (valueMap Φ i)) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [squareBottomArrow_edge]
  change SSet.yonedaEquiv (squareBottomEdge ≫
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare p q i r h ≫ Φ)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare_bottom,
    SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply, ← valueMap_edge]
  rfl

lemma top_arrow : Arrow.mk (squareHoTop (square Φ p q i r h)) =
    Arrow.mk (SpectrumHo.hom (valueMap Φ (IdentityLax.exactDiagonal Q))) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [squareTopArrow_edge]
  change SSet.yonedaEquiv (squareTopEdge ≫
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare p q i r h ≫ Φ)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare_top,
    SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply, ← valueMap_edge]
  rfl

lemma left_arrow : Arrow.mk (squareHoLeft (square Φ p q i r h)) =
    Arrow.mk (SpectrumHo.hom (valueMap Φ (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.kernelMap p q i r))) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [squareLeftArrow_edge]
  change SSet.yonedaEquiv (squareLeftEdge ≫
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare p q i r h ≫ Φ)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare_left,
    SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply, ← valueMap_edge]
  rfl

lemma right_arrow : Arrow.mk (squareHoRight (square Φ p q i r h)) =
    Arrow.mk (SpectrumHo.hom (valueMap Φ (LaxUniversalDifference.exactLift p q r))) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [squareRightArrow_edge]
  change SSet.yonedaEquiv (squareRightEdge ≫
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare p q i r h ≫ Φ)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare_right,
    SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply, ← valueMap_edge]
  rfl

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalValue
