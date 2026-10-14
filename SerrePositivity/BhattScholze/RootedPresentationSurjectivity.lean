module

public import SerrePositivity.BhattScholze.CompatibleRootFamilyCompletionPerfectoid

/-! # B4-6：根付き生成族による全射商の全射性

核の全元の根は要求せず、核を生成する族の初項の根を使う。
これにより、根付き拡大の入力を元の核の生成族だけに制限できる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S C σ : Type u}
variable [CommRing R] [CommRing S] [CommRing C]

/-- 核が根族の初項で生成される全射商の任意のperfectoid化は全射。
核の全元の根・生成族の有限性・商のp正則性・完備性は不要。 -/
theorem surjective_of_isPerfectoidization_of_rootedPresentation
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (hk : RingHom.ker q = compatibleRootFamilyZeroIdeal ρ)
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  let e : R ⧸ compatibleRootFamilyZeroIdeal ρ ≃+* S :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hq)
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
    · intro k hk'
      apply huniq
      apply RingHom.ext
      intro s
      have hs := RingHom.congr_fun hk' (e.symm s)
      change k (f (e (e.symm s))) = g (e.symm s) at hs
      rw [e.apply_symm_apply] at hs
      exact hs
  have hs := surjective_of_isPerfectoidization_of_compatibleRootFamily hR ρ hρ
    (f.comp e.toRingHom) hfe
  intro c
  obtain ⟨x, hx⟩ := hs c
  exact ⟨e x, hx⟩

end SerrePositivity.BhattScholze
