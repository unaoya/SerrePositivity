module

public import SerrePositivity.BhattScholze.DeltaRootSourceSequentialTor
public import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction

/-! # G10による実冪剰余の離散性と平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) (n : ℕ) (hn : 0 < n)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
  (hd : IsSMulRegular A d) (v : Aˣ) (hv : (v : A) = D.delta d)
local notation "Tₙ" => A ⧸ Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n))))))
  (DeltaRootSourceIteratedPDCompletion D d b)

include hn hpA hd v hv in
/-- 実Tₙ還元は次数零に集中し、そのH0はTₙ上平坦。 -/
theorem deltaRootSourcePowerResidue_pure_flat :
    (Y₀).obj.IsGE 0 ∧ (Y₀).obj.IsLE 0 ∧
      Module.Flat Tₙ ((DerivedCategory.homologyFunctor (ModuleCat Tₙ) 0).obj (Y₀).obj) := by
  have hPure := deltaRootSourceCanonicalPowerResidue_homology_isZero D d b n hn hpA hd v hv
  have hFF := deltaRootSourceCanonicalPowerResidueH0_faithfullyFlat D d b n hn hpA hd v hv
  let := hFF
  exact derived_pure_flat_of_nilpotent_reduction Kₙ Y₀ hPure
    inferInstance ⟨n, prismaticPowerResidueIdeal_pow (p : A) d n⟩

include hn hpA hd v hv in
/-- G10で得た実冪剰余の非零次数ホモロジー消滅。 -/
theorem deltaRootSourcePowerResidue_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Tₙ) i).obj (Y₀).obj) := by
  obtain ⟨hGE, hLE, _⟩ := deltaRootSourcePowerResidue_pure_flat D d b n hn hpA hd v hv
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

include hn hpA hd v hv in
/-- 実冪剰余のH0平坦性。 -/
theorem deltaRootSourcePowerResidueH0_flat :
    Module.Flat Tₙ ((DerivedCategory.homologyFunctor (ModuleCat Tₙ) 0).obj (Y₀).obj) :=
  (deltaRootSourcePowerResidue_pure_flat D d b n hn hpA hd v hv).2.2

end SerrePositivity.BhattScholze
