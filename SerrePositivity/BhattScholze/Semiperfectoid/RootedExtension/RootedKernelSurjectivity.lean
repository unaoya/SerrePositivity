module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.RootedIdealSurjectivity

/-! # B4-5：根を持つ核を持つ全射商のperfectoid化

全射な環準同型を、その実際の核の商に同定して根付きイデアルの結果を適用する。
一般全射商の全射性を引用せず、核の両立する根を明示して入力する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S C : Type u}
variable [CommRing R] [CommRing S] [CommRing C]

/-- perfectoid環の全射商の核の各元が両立する根を持てば、任意のperfectoid化は全射。
商の完備性・p正則性・核の有限生成性は要求しない。 -/
theorem surjective_of_isPerfectoidization_of_rootedKernel
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (ρ : RingHom.ker q → ℕ → R) (hρ0 : ∀ s, ρ s 0 = (s : R))
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  let e : R ⧸ RingHom.ker q ≃+* S := RingHom.quotientKerEquivOfSurjective hq
  have hfe : IsPerfectoidization p (f.comp e.toRingHom) := hf.precomp_ringEquiv e
  have hs := surjective_of_isPerfectoidization_of_rootedIdeal hR (RingHom.ker q)
    ρ hρ0 hρ (f.comp e.toRingHom) hfe
  intro c
  obtain ⟨x, hx⟩ := hs c
  exact ⟨e x, hx⟩

end SerrePositivity.BhattScholze
