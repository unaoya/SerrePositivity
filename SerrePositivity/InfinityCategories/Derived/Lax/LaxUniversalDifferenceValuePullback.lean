module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifferenceOuter
public import SerrePositivity.InfinityCategories.Stable.PullbackPasting
public import SerrePositivity.InfinityCategories.F1.SquareDuality

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference
open SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r) {Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}}
  (hΦ : IsLocalizingInvariant Φ)

include hΦ in
theorem comparisonSquare_value_isPullback :
    IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare p q i r h ≫ Φ) := by
  let F := (rectangle p q i r h).diagram ≫ Φ
  have hR : IsPullbackSquare (pastingSquare F 0) := by
    have ht := (isPullbackSquare_iff_transpose ((identityDiagram Q).square ≫ Φ)).mp
      (hΦ.preservesVerdier (identityDiagram Q))
    change IsPullbackSquare (pastingSquare (rectangle p q i r h).diagram 0 ≫ Φ)
    rw [(rectangle p q i r h).right_eq]
    simpa only [Category.assoc] using ht
  have hO : IsPullbackSquare (pastingSquare F 1) := by
    have ht := (isPullbackSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare p q i r h ≫ Φ)).mp
      (hΦ.preservesVerdier (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerDiagram p q i r h))
    change IsPullbackSquare (pastingSquare (rectangle p q i r h).diagram 1 ≫ Φ)
    simpa only [_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.outerSquare, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp] using ht
  have hL := isPullbackSquare_pasting_cancel_right F hR hO
  change IsPullbackSquare (pastingSquare (rectangle p q i r h).diagram 2 ≫ Φ) at hL
  rw [(rectangle p q i r h).left_eq] at hL
  apply (isPullbackSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare p q i r h ≫ Φ)).mpr
  simpa only [Category.assoc] using hL

end SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.comparisonSquare_value_isPullback := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalDifference.comparisonSquare_value_isPullback
