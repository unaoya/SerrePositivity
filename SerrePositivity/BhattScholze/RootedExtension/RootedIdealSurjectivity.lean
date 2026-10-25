module

public import SerrePositivity.BhattScholze.RootedExtension.CompatibleRoot.CompatibleRootFamilyCompletionPerfectoid

/-! # B4-4：任意イデアルの全元が根を持つ場合の全射性

有限生成への帰着を使わず、Jの全元を根族の添字とする。
根付き拡大の存在はこの定理の仮定であり、Andréの引用は使わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Jの各元を最初の元に持つ根族は、最初の元のイデアルとしてJそのものを生成する。 -/
theorem compatibleRootFamilyZeroIdeal_eq_of_roots_on_ideal
    (J : Ideal R) (ρ : J → ℕ → R) (hρ0 : ∀ s, ρ s 0 = (s : R)) :
    compatibleRootFamilyZeroIdeal ρ = J := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change ρ s 0 ∈ J
    rw [hρ0]
    exact s.property
  · intro x hx
    have hh : ρ ⟨x, hx⟩ 0 = x := hρ0 ⟨x, hx⟩
    rw [← hh]
    exact Ideal.mem_span_range_self

/-- 任意イデアルの全元が両立する根を持てば、その商の任意の普遍perfectoid化は全射。
元族・イデアルの有限生成性、商のp正則性・完備性を仮定しない。 -/
theorem surjective_of_isPerfectoidization_of_rootedIdeal
    (hR : IsIntegralPerfectoid R p) (J : Ideal R) (ρ : J → ℕ → R)
    (hρ0 : ∀ s, ρ s 0 = (s : R)) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    {C : Type u} [CommRing C] (f : R ⧸ J →+* C) (hf : IsPerfectoidization p f) :
    Function.Surjective f := by
  have hJ := compatibleRootFamilyZeroIdeal_eq_of_roots_on_ideal J ρ hρ0
  let e : R ⧸ J ≃+* R ⧸ compatibleRootFamilyZeroIdeal ρ := Ideal.quotEquivOfEq hJ.symm
  let ff := f.comp e.symm.toRingHom
  have hff : IsPerfectoidization p ff := hf.precomp_ringEquiv e.symm
  have hsurj := surjective_of_isPerfectoidization_of_compatibleRootFamily hR ρ hρ ff hff
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  exact ⟨e.symm y, hy⟩

end SerrePositivity.BhattScholze
