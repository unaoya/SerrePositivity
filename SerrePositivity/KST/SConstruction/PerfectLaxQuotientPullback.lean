module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientOuter
public import SerrePositivity.KST.SConstruction.PerfectLocalizingInvariant
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PullbackPasting
public import SerrePositivity.InfinityCategories.HA.Section6_1_1.SquareDuality

/-! # 完備化後の商の普遍差比較の不変量値は引き戻し
概要：Cat^perf の同じ比較正方形の値が、実 Sp の引き戻しになることを証明する。
方針：同じ長方形の右面・外周を元の Verdier 図式として読み、pullback 消去則を使う。
規約：完備化後の射の厳密商性や不変量の拡張を要求しない。使われ方：LT の切除。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 指定比較道と元の全単体を持つ正方形の、同じ不変量による像。 -/
def universalValueSquare (F : perfectStableInfinity.{u} ⟶ Sp.{u}) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := d.universalSquare ≫ F

include hF in
/-- 同じ比較正方形の値は、二つの元の実 fiber 列の消去により引き戻し。 -/
theorem universalValueSquare_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.universalValueSquare F) := by
  let G := d.rectangleDiagram ≫ F
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare G 0) := by
    have ht := (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose
      ((perfectIdentityLaxSequence d.sequence.right
        d.sequence.right_complete).presentation.square ≫ F)).mp
          (hF.preservesVerdier
            (perfectIdentityLaxSequence d.sequence.right d.sequence.right_complete).presentation)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.rectangleDiagram 0 ≫ F)
    rw [d.rectangleDiagram_right]
    simpa only [Category.assoc] using ht
  have hO : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare G 1) := by
    have ht := (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose (d.outerSquare ≫ F)).mp
      (hF.preservesVerdier d.outerDiagram)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.rectangleDiagram 1 ≫ F)
    simpa only [outerSquare, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp] using ht
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isPullbackSquare_pasting_cancel_right G hR hO
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.rectangleDiagram 2 ≫ F) at hL
  rw [d.rectangleDiagram_left] at hL
  apply (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose (d.universalValueSquare F)).mpr
  simpa only [universalValueSquare, Category.assoc] using hL

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
