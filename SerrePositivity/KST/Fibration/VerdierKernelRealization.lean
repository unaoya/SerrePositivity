module
public import SerrePositivity.KST.Fibration.VerdierKernelEquivalence
public import SerrePositivity.KST.SConstruction.MultiRealizationEquivalence

/-! # 元の Verdier 包含と実際の核の全正有限反復実現での同値 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の核への制限は、全正有限反復実現で同じ元の射を局所化同型にする。 -/
theorem verdierKernelExact_multiRealization_localized_isIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (verdierKernelExact h))) :=
  multiRealization_map_localized_isIso_of_equivalence r (verdierKernelEquivalence h)

/-- 核部分圏を介しても、元の包含の全反復実現射を厳密に回収する。 -/
lemma verdierKernelExact_realization_inclusion
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r : ℕ) :
    (multiRealizationFunctor r).map (verdierKernelExact h) ≫
      (multiRealizationFunctor r).map (closedStableInclusion (kernelClosedPredicate q)) =
        (multiRealizationFunctor r).map (sInputExactMap i) := by
  rw [← Functor.map_comp]
  exact congrArg (multiRealizationFunctor r).map (Subtype.ext (verdierKernelExact_ι h))

end SerrePositivity.KST.Fibration
