module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientExactFunctorEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableClosureInclusion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableVerdierSequence
/-!
概要：実安定閉包の包含と平坦 Drinfeld 商の射影は安定 ∞ 圏の Verdier 列をなす。
方針：包含の完全充満忠実性、商の零化と全完全関手圏の同値を接続する。
規約：局所 K-flat 条件を保持。使われ方：平坦分解後の一般の Verdier 列への移送。
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
/-- 実安定閉包の完全充満包含と、局所平坦な実 dg 商がなす Verdier 列。 -/
theorem dgQuotient_isStableVerdierSequence (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) :
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A D
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve_isStable A D P
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve_isStable A D P hP
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsStableVerdierSequence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion A D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve_isStable A D P
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve_isStable A D P hP
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor A D P hP
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion_isFullyFaithful A D P,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion_isExactFunctor A D P, inferInstance, ?_, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion_kills A D P _
      (fun x hx => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_kills A D P ⟨x, hx⟩)
  · intro Y _ _
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition_isQCatEquivalence
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientPrecomposition_isFullyFaithful A D P hP Y
    · intro F hF hkill
      have hk := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion_kills_iff A D P F).mp
        (fun z => hkill _ ⟨z, rfl⟩)
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierExactFunctor_extension_exists A D P hP F (fun b => hk b.val b.property)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
