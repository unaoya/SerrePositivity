module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierPullback

public import SerrePositivity.KST.LocalizingInvariants.RelativeInvariant
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PullbackPasting
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareTranspose

/-!
概要：提示源内の Verdier 比較長方形から、同じ値関手の実 pullback を導く。
方針：右面・外周の転置 Verdier 提示を E で写し、実 pullback 貼合せで右面を消す。
規約：長方形と全合成三角形を S 内で保持する。使われ方：相対版 K-8 d8。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

namespace RelativeVerdierRectangle
variable {S : SSet.{u + 1}} {ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}}
  (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierRectangle ν)

/-- fiber 列二つから得る d8 の比較 pullback。E の絶対版への延長は不要。 -/
lemma comparisonSquare_isPullback {E : S ⟶ Spectra.Sp.{u}}
    (hE : IsRelativeLocalizingInvariant ν E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.comparisonSquare ≫ E) := by
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (d.diagram ≫ E) 0) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 0 ≫ E)
    rw [d.right_eq]
    exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose (d.right.square ≫ E)).mp
      (hE.preservesVerdier d.right)
  have hO : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (d.diagram ≫ E) 1) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 1 ≫ E)
    rw [d.outer_eq]
    exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose (d.outer.square ≫ E)).mp
      (hE.preservesVerdier d.outer)
  exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 2 ≫ E)).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isPullbackSquare_pasting_cancel_right (d.diagram ≫ E) hR hO)

/-- 元の E 値の同じ cospan 上の実極限錐。 -/
def comparisonCone (E : S ⟶ Spectra.Sp.{u}) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (d.comparisonSquare ≫ E)

lemma comparisonCone_isLimit {E : S ⟶ Spectra.Sp.{u}}
    (hE : IsRelativeLocalizingInvariant ν E) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((_root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.comparisonCone d) E) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.comparisonSquare_isPullback d) hE

end RelativeVerdierRectangle
end SerrePositivity.KST.LocalizingInvariants
