module
public import SerrePositivity.KST.SConstruction.DGStandardExactness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-! # 同じ厳密 dg 関手の native・標準 DK 同値判定
概要：元の native dg nerve 射の同値性を、同じ標準 DK coherent 射で判定する。
方針：既存の比較同値と元の厳密な自然性を合成し、両側で同値を消去する。
規約：元の dg 関手を変更しない。使われ方：実 Perf ラベル作用の Morita 同値性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- 元の厳密 dg 射の native 同値性は、同じ標準 DK coherent 射と同値。 -/
lemma dgNerve_map_isQCatEquivalence_iff_standard (F : DGFunctor A D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgStandardCoherentMap F) := by
  have hd := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparisonEquivalence (R := A) (D := D)).isQCatEquivalence
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparisonEquivalence (R := A) (D := E)).isQCatEquivalence
  constructor
  · intro hf
    have h := hd.comp hf
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := A) (D := D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) at h
    rw [← dgCoherentComparison_naturality F] at h
    exact he.cancel_right h
  · intro hf
    have h := hf.comp he
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (dgStandardCoherentMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := A) (D := E)) at h
    rw [dgCoherentComparison_naturality F] at h
    exact hd.cancel_left h

end SerrePositivity.KST.SConstruction
