module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.PerfectPrismRootedPerfectoidExtension
public import SerrePositivity.BhattScholze.Semiperfectoid.SemiperfectoidPerfectoidization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison

/-! # B4：導来p完備なperfectoid環の全射商の普遍perfectoid化は全射 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S C : Type u}
variable [CommRing R] [CommRing S] [CommRing C]

/-- 任意perfectoid環の導来p完備な全射商の、任意の普遍perfectoid化は全射。
pねじれのない商・有限性・古典的完備性は仮定しない。 -/
theorem surjective_of_isPerfectoidization_of_semiperfectoid_quotient
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  rcases hR with hs | ⟨hp, hc, ⟨π, u, hu⟩, hF, hker⟩
  · let := hs
    let : Subsingleton S := q.codomain_trivial
    let : Subsingleton C := f.codomain_trivial
    exact fun y => ⟨0, Subsingleton.elim _ _⟩
  · let := hc
    let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    obtain ⟨d, hd, e, _⟩ := exists_perfectoidTrialPrism R p hF hker π u hu
    let := DerivedCompletion.pdCompletionCommRing (WittVector p (PreTilt R p)) p d
    let P := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    have hP := perfectDeltaPDPrism_isPerfect (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    exact surjective_of_isPerfectoidization_of_perfectPrism_quotient P hP
      (q.comp e.toRingHom) (hq.comp e.surjective) hS f hf

/-- B3の一般存在・普遍性とB4により、一般の導来p完備商は全射perfectoid化を持つ。 -/
theorem exists_surjective_perfectoidization_of_semiperfectoid_quotient
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C),
      IsPerfectoidization p f ∧ Function.Surjective f := by
  obtain ⟨C, hC, f, hf⟩ := exists_perfectoidization_of_semiperfectoid_quotient hR q hq hS
  let := hC
  exact ⟨C, hC, f, hf,
    surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR q hq hS f hf⟩

/-- 古典的p進完備な商への互換入口。共通の比較により商のp正則性は不要。 -/
theorem surjective_of_isPerfectoidization_of_adic_complete_quotient
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f :=
  surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR q hq
    (DerivedCompletion.isModuleComplete_of_isAdicComplete S (p : S) (ModuleCat.of S S)) f hf

end SerrePositivity.BhattScholze
