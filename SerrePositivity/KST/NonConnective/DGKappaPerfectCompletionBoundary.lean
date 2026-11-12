module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectIdempotentCompleteGeneral
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompleteImageRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
概要：B′検討のため、現行 P の向きでの冪等完備化は同値に戻ることを検証する。
方針：始域の実 Perf の冪等完備性で、像の retract を元の像に戻す。
規約：模型変更を実装しない。核→Perf の逆向きの完備化とは区別する。
使われ方：K-7 c4・c5・e の P 供給境界変更の型検査。
-/
@[expose] public noncomputable section
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 現行 P の始域 Perf を保持すると、同じ向きの冪等完備化は全関手同値を与える。 -/
theorem dgKappaPerfectComparison_equivalence_of_idempotentCompletion
    {E : SSet.{max (u + 1) v}} [Quasicategory E]
    (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D ⟶ E)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective f hf.2.1
  intro y
  obtain ⟨x, hx⟩ := hf.2.2 y
  obtain ⟨z, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R D).retract_iso_in_image
    f hf.2.1 x y hx.some
  exact ⟨z, ⟨e.symm⟩⟩

end SerrePositivity.KST.NonConnective
