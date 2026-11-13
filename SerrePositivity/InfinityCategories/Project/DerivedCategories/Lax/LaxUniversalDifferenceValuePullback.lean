module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceOuter
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PullbackPasting
public import SerrePositivity.InfinityCategories.HA.Section6_1_1.SquareDuality

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r) {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}}
  (hΦ : IsLocalizingInvariant Φ)

include hΦ in
theorem comparisonSquare_value_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h ≫ Φ) := by
  let F := (rectangle p q i r h).diagram ≫ Φ
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) := by
    have ht := (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose ((identityDiagram Q).square ≫ Φ)).mp
      (hΦ.preservesVerdier (identityDiagram Q))
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (rectangle p q i r h).diagram 0 ≫ Φ)
    rw [(rectangle p q i r h).right_eq]
    simpa only [Category.assoc] using ht
  have hO : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) := by
    have ht := (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare p q i r h ≫ Φ)).mp
      (hΦ.preservesVerdier (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerDiagram p q i r h))
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (rectangle p q i r h).diagram 1 ≫ Φ)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerSquare, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp] using ht
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isPullbackSquare_pasting_cancel_right F hR hO
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (rectangle p q i r h).diagram 2 ≫ Φ) at hL
  rw [(rectangle p q i r h).left_eq] at hL
  apply (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h ≫ Φ)).mpr
  simpa only [Category.assoc] using hL

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.comparisonSquare_value_isPullback := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.comparisonSquare_value_isPullback
