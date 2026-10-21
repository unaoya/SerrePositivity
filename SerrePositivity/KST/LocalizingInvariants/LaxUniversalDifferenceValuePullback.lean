module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifferenceOuter
public import SerrePositivity.InfinityCategories.Stable.PullbackPasting
public import SerrePositivity.InfinityCategories.Stable.SquareDuality

/-!
概要：一般商と恒等 lax 差を比較する元の正方形の値は、実 pullback である。
方針：長方形の右面・外周が Verdier 列の像の fiber なので、pullback 貼り合わせで消す。
規約：Sp の安定性も整数 π だけの同値判定も使わない。使われ方：元の二脚の切除。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r) {Φ : StableInfinity.{u} ⟶ Sp.{u}}
  (hΦ : IsLocalizingInvariant Φ)

include hΦ in
theorem comparisonSquare_value_isPullback :
    IsPullbackSquare (comparisonSquare p q i r h ≫ Φ) := by
  let F := (rectangle p q i r h).diagram ≫ Φ
  have hR : IsPullbackSquare (pastingSquare F 0) := by
    have ht := (isPullbackSquare_iff_transpose ((identityDiagram Q).square ≫ Φ)).mp
      (hΦ.preservesVerdier (identityDiagram Q))
    change IsPullbackSquare (pastingSquare (rectangle p q i r h).diagram 0 ≫ Φ)
    rw [(rectangle p q i r h).right_eq]
    simpa only [Category.assoc] using ht
  have hO : IsPullbackSquare (pastingSquare F 1) := by
    have ht := (isPullbackSquare_iff_transpose (outerSquare p q i r h ≫ Φ)).mp
      (hΦ.preservesVerdier (outerDiagram p q i r h))
    change IsPullbackSquare (pastingSquare (rectangle p q i r h).diagram 1 ≫ Φ)
    simpa only [outerSquare, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp] using ht
  have hL := isPullbackSquare_pasting_cancel_right F hR hO
  change IsPullbackSquare (pastingSquare (rectangle p q i r h).diagram 2 ≫ Φ) at hL
  rw [(rectangle p q i r h).left_eq] at hL
  apply (isPullbackSquare_iff_transpose (comparisonSquare p q i r h ≫ Φ)).mpr
  simpa only [Category.assoc] using hL

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
