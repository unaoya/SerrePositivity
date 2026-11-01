module
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientExactDescent
public import SerrePositivity.InfinityCategories.Derived.DGStableClosureInclusion
public import SerrePositivity.InfinityCategories.Stable.Verdier.StableVerdierSequence
/-!
概要：実安定閉包の包含と平坦分解後の商は安定 ∞ 圏の Verdier 列をなす。
方針：包含の完全充満忠実性、商の零化と全完全関手圏の同値を接続する。
規約：元の Hom の平坦性を要求しない。使われ方：非可換導来 ∞ 圏の Verdier 列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 実安定閉包の完全充満包含と、元の Hom の平坦性を仮定しない実商の Verdier 列。 -/
theorem resolvedDGQuotient_isStableVerdierSequence (P : Set D) :
    let := dgNerve_isStable_of_pretriangulated A D
    let := dgStableClosureNerve_isStable A D P
    let := resolvedDGQuotientNerve_isStable A D P
    IsStableVerdierSequence (dgStableClosureInclusion A D P)
      (resolvedDGQuotientFunctor A D P) := by
  let := dgNerve_isStable_of_pretriangulated A D
  let := dgStableClosureNerve_isStable A D P
  let := resolvedDGQuotientNerve_isStable A D P
  let := resolvedDGQuotientFunctor_isExactFunctor A D P
  refine ⟨dgStableClosureInclusion_isFullyFaithful A D P,
    dgStableClosureInclusion_isExactFunctor A D P, inferInstance, ?_, ?_⟩
  · exact dgStableClosureInclusion_kills A D P _
      (fun x hx => resolvedDGQuotientFunctor_kills A D P ⟨x, hx⟩)
  · intro Y _ _
    apply zeroingExactPrecomposition_isQCatEquivalence
    · exact resolvedDGQuotientPrecomposition_isFullyFaithful A D P Y
    · intro F hF hkill
      have hk := (dgStableClosureInclusion_kills_iff A D P F).mp
        (fun z => hkill _ ⟨z, rfl⟩)
      exact resolvedDGVerdierExactFunctor_extension_exists A D P F (fun b => hk b.val b.property)
end SerrePositivity.InfinityCategories
