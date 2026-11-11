module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedPerfectComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectIdempotentCompleteGeneral

/-!
概要：同じ D-9 実小核の native nerve に、P の元の Perf の coherent 冪等完備性を移す。
方針：P と同じ制限増大の比較による全写像空間の同値を使う。
規約：明示 I・P に条件付き。実小核からその Perf 完備化への Yoneda 比較とは区別する。
使われ方：K-7 c5 の元の Perf・P 照合における、完備化前の実核の性質の検証。
-/

@[expose] public section
noncomputable section
universe u v
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (P : DGKappaPerfectInput R D I)

include P in
/-- I・P に条件付きで、同じ実小核の native nerve は coherent 冪等完備。 -/
theorem dgKappaResolvedKernelNerve_isIdempotentComplete :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (dgKappaResolvedKernelKInput R D I)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R D).of_equivalence
    (dgKappaPerfectResolvedComparison_isQCatEquivalence R D I P).choose

end SerrePositivity.KST.NonConnective
