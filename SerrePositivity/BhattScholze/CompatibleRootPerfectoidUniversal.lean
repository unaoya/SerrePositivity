module

public import SerrePositivity.BhattScholze.CompatibleRootQuotient
public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionFrobenius
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationUniqueness

/-! # B4-1：根付き商の任意perfectoid試験環への普遍性

既存の根イデアル商の普遍性に、一般perfectoid環の被約性と完備性を供給する。
候補のperfectoid性は別工程の仮定として明示する。Andréの引用は使わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 根付き商から任意perfectoid環への射は、根イデアル商の完備化を一意に経由する。
零試験環も共通の被約性・完備性の定理で扱う。 -/
theorem existsUnique_compatibleRootCompletionLift_to_perfectoid
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {T : Type u} [CommRing T] (hT : IsIntegralPerfectoid T p)
    (g : R ⧸ Ideal.span {ρ 0} →+* T) :
    ∃! l : CompatibleRootCompletion p ρ →+* T,
      l.comp (compatibleRootCompletionMap p ρ) = g := by
  let := hT.isReduced T p
  let := hT.isAdicComplete T p
  exact existsUnique_compatibleRootCompletionLift ρ hρ g

/-- 候補のperfectoid性を別途証明すれば、具体的な標準射はperfectoid化である。 -/
theorem compatibleRootCompletionMap_isPerfectoidization_of_isIntegralPerfectoid
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hC : IsIntegralPerfectoid (CompatibleRootCompletion p ρ) p) :
    IsPerfectoidization p (compatibleRootCompletionMap p ρ) := by
  refine ⟨hC, ?_⟩
  intro T _ hT g
  exact existsUnique_compatibleRootCompletionLift_to_perfectoid ρ hρ hT g

/-- 根付き商の任意の普遍perfectoid化は、候補のperfectoid性の下で標準候補と同型。 -/
theorem exists_compatibleRootCompletionEquiv_of_isPerfectoidization
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hC : IsIntegralPerfectoid (CompatibleRootCompletion p ρ) p)
    {C : Type u} [CommRing C] (f : R ⧸ Ideal.span {ρ 0} →+* C)
    (hf : IsPerfectoidization p f) :
    ∃ e : CompatibleRootCompletion p ρ ≃+* C,
      e.toRingHom.comp (compatibleRootCompletionMap p ρ) = f :=
  let h := compatibleRootCompletionMap_isPerfectoidization_of_isIntegralPerfectoid ρ hρ hC
  h.exists_equiv p hf

end SerrePositivity.BhattScholze
