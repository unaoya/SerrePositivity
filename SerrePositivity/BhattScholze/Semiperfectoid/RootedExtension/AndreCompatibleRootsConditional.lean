module

public import SerrePositivity.BhattScholze.Inputs.AndreFlatness

/-! # B4cの条件付き入力：任意元族の両立する根

既存の名前付きAndré引用から導く途中成果。B4の引用解消ではない。
引用なしの根付き拡大の構成は別工程として残す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze

/-- 既存André入力に相対的に、任意元族の根を持つp完全忠実平坦perfectoid拡大が存在する。
この定理の公理依存には既存Inputs.AndreFlatnessのsorryAxが残る。 -/
theorem exists_completelyFaithfullyFlat_compatibleRoots_of_andre
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (σ : Type u) (a : σ → R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      IsIntegralPerfectoid S p ∧ IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S ∧
        ∃ ρ : σ → ℕ → S,
          (∀ s, ρ s 0 = algebraMap R S (a s)) ∧
          ∀ s n, ρ s (n + 1) ^ p = ρ s n := by
  obtain ⟨S, hSring, hSalg, hS, hflat, haic⟩ :=
    Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed R p hR
  let := hSring
  let := hSalg
  have hroots : ∀ s : σ, ∃ ρ : ℕ → S,
      ρ 0 = algebraMap R S (a s) ∧ ∀ n, ρ (n + 1) ^ p = ρ n :=
    fun s ↦ haic.exists_compatible_pow_roots (Fact.out : p.Prime).pos (algebraMap R S (a s))
  choose ρ hρ0 hρ using hroots
  exact ⟨S, hSring, hSalg, hS, hflat, ρ, hρ0, hρ⟩

end SerrePositivity.BhattScholze
