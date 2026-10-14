module

public import SerrePositivity.BhattScholze.RootedIdealSurjectivity

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
  have hfe : IsPerfectoidization p (f.comp e.toRingHom) := by
    refine ⟨hf.1, ?_⟩
    intro T _ hT g
    obtain ⟨l, hl, huniq⟩ := hf.2 T hT (g.comp e.symm.toRingHom)
    refine ⟨l, ?_, ?_⟩
    · apply RingHom.ext
      intro x
      have hx := RingHom.congr_fun hl (e x)
      change l (f (e x)) = g (e.symm (e x)) at hx
      rw [e.symm_apply_apply] at hx
      exact hx
    · intro k hk
      apply huniq
      apply RingHom.ext
      intro s
      have hs := RingHom.congr_fun hk (e.symm s)
      change k (f (e (e.symm s))) = g (e.symm s) at hs
      rw [e.apply_symm_apply] at hs
      exact hs
  have hs := surjective_of_isPerfectoidization_of_rootedIdeal hR (RingHom.ker q)
    ρ hρ0 hρ (f.comp e.toRingHom) hfe
  intro c
  obtain ⟨x, hx⟩ := hs c
  exact ⟨e x, hx⟩

end SerrePositivity.BhattScholze
