module
public import SerrePositivity.KST.SConstruction.DGStandardExactness
public import SerrePositivity.KST.SConstruction.FunctorIsoEquivalenceReflection

/-! # 同じ標準 DK 関手同型から元の native dg 関手同型へ
概要：二つの厳密 dg 関手の標準 coherent 同型を、元の native nerve 射の同型へ戻す。
方針：標的比較で後合成し、厳密な比較自然性と源の実同値による反映を使う。
規約：同じ元の dg 関手を保持する。使われ方：実 Perf 評価の native 四角形。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- 同じ標準 DK 同型は、元の二つの native dg nerve 射の関手同型を与える。 -/
def dgStandardFunctorIso_to_native {F G : DGFunctor A D E}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgStandardCoherentMap F) (dgStandardCoherentMap G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) := by
  have he := h.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := A) (D := E))
  rw [dgCoherentComparison_naturality F, dgCoherentComparison_naturality G] at he
  exact functorIsoReflectPreEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparisonEquivalence (R := A) (D := D)) he

end SerrePositivity.KST.SConstruction
