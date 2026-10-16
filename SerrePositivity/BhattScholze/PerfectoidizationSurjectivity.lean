module

public import SerrePositivity.BhattScholze.Inputs.SemiperfectoidSurjectivity
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationUniqueness

/-! # 証明済みsemiperfectoid全射性から任意の普遍対象への移送 -/

public section
universe u
namespace SerrePositivity.BhattScholze

/-- 証明済みの全射perfectoid化から、任意の普遍perfectoid化へ全射性を移す。 -/
theorem surjective_of_isPerfectoidization_of_complete_torsionFree_quotient
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    (hp : Function.Injective (fun x : S ↦ (p : S) * x))
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  obtain ⟨D, hD, g, hg, hgs⟩ :=
    Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotient R S p hR q hq hp
  let := hD
  exact (hg.surjective_iff p hf).mp hgs

end SerrePositivity.BhattScholze
