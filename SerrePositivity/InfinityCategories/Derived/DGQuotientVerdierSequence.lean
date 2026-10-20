module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientExactFunctorEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGStableClosureInclusion
public import SerrePositivity.InfinityCategories.Derived.StableVerdierSequence
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 実安定閉包の完全充満包含と、局所平坦な実 dg 商がなす Verdier 列。 -/
theorem dgQuotient_isStableVerdierSequence (P : Set D) (hP : DGQuotient.localKFlat A D P) :
    let := dgNerve_isStable_of_pretriangulated A D
    let := dgStableClosureNerve_isStable A D P
    let := dgQuotientNerve_isStable A D P hP
    IsStableVerdierSequence (dgStableClosureInclusion A D P)
      (dgQuotientNerveProjection A D P) := by
  let := dgNerve_isStable_of_pretriangulated A D
  let := dgStableClosureNerve_isStable A D P
  let := dgQuotientNerve_isStable A D P hP
  let := dgQuotientNerveProjection_isExactFunctor A D P hP
  refine ⟨dgStableClosureInclusion_isFullyFaithful A D P,
    dgStableClosureInclusion_isExactFunctor A D P, inferInstance, ?_, ?_⟩
  · exact dgStableClosureInclusion_kills A D P _
      (fun x hx => dgQuotientNerveProjection_kills A D P ⟨x, hx⟩)
  · intro Y _ _
    apply zeroingExactPrecomposition_isQCatEquivalence
    · exact dgQuotientPrecomposition_isFullyFaithful A D P hP Y
    · intro F hF hkill
      have hk := (dgStableClosureInclusion_kills_iff A D P F).mp
        (fun z => hkill _ ⟨z, rfl⟩)
      exact dgVerdierExactFunctor_extension_exists A D P hP F (fun b => hk b.val b.property)
end SerrePositivity.InfinityCategories
