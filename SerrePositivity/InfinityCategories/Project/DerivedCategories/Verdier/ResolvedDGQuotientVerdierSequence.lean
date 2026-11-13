module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientExactDescent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableClosureInclusion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableVerdierSequence
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 実安定閉包の完全充満包含と、元の Hom の平坦性を仮定しない実商の Verdier 列。 -/
theorem resolvedDGQuotient_isStableVerdierSequence (P : Set D) :
    let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated A D
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve_isStable A D P
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable A D P
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsStableVerdierSequence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion A D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P) := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve_isStable A D P
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable A D P
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isExactFunctor A D P
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion_isFullyFaithful A D P,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion_isExactFunctor A D P, inferInstance, ?_, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion_kills A D P _
      (fun x hx => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_kills A D P ⟨x, hx⟩)
  · intro Y _ _
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition_isQCatEquivalence
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientPrecomposition_isFullyFaithful A D P Y
    · intro F hF hkill
      have hk := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion_kills_iff A D P F).mp
        (fun z => hkill _ ⟨z, rfl⟩)
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGVerdierExactFunctor_extension_exists A D P F (fun b => hk b.val b.property)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
