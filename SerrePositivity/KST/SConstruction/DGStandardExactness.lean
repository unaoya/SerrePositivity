module
public import SerrePositivity.KST.SConstruction.DGCoherentComparisonNaturality
public import SerrePositivity.KST.SConstruction.ExactnessEquivalenceReflection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComparisonEquivalence

/-! # 元の dg 射と標準 DK 射の完全性の一致
概要：同じ厳密 dg 関手の native nerve と標準 coherent nerve の完全性は同値である。
方針：元の DK 比較の厳密自然性と、両端の実比較同値による完全性の反映を使う。
規約：対象の宇宙を縮小せず Small 仮定も置かない。使われ方：Perf 比較の完全性の移送。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- 同じ元の厳密 dg 関手の完全性は、標準 DK coherent nerve 上でも判定できる。 -/
lemma dgNerve_map_isExactFunctor_iff_standard (F : DGFunctor A D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgStandardCoherentMap F) := by
  have h := (isExactFunctor_equivalence_comp_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparisonEquivalence (R := A) (D := D)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)).symm
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := A) (D := D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) at h
  rw [← dgCoherentComparison_naturality F] at h
  exact h.trans (isExactFunctor_comp_equivalence_iff (dgStandardCoherentMap F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparisonEquivalence (R := A) (D := E)))

end SerrePositivity.KST.SConstruction
