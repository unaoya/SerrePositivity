module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.CompatibleRoot.CompatibleRootPDComparison
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.CompatibleRoot.CompatibleRootSingletonComparison
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.CompatibleRoot.CompatibleRootFamilyCompletionPerfectoid

/-! # B4a：根付き単項商の完備化のperfectoid性

既存の単一根候補と標準射を保ち、一元添字の根族候補との比較からperfectoid性を得る。
Andréの引用・一般全射性・B5を使わない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- perfectoid環の両立する根をすべて消した商のp完備化はperfectoid。
一般のpねじれと零環も含む。 -/
theorem compatibleRootCompletion_isIntegralPerfectoid
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    IsIntegralPerfectoid (CompatibleRootCompletion p ρ) p := by
  exact isIntegralPerfectoid_of_ringEquiv p (compatibleRootSingletonCompletionEquiv p ρ)
    (compatibleRootFamilyCompletion_isIntegralPerfectoid hR
      (fun _ : PUnit.{u+1} ↦ ρ) (fun _ ↦ hρ))

/-- 根を持つ単項商の具体的標準射はperfectoid化。 -/
theorem compatibleRootCompletionMap_isPerfectoidization
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    IsPerfectoidization p (compatibleRootCompletionMap p ρ) :=
  compatibleRootCompletionMap_isPerfectoidization_of_isIntegralPerfectoid ρ hρ
    (compatibleRootCompletion_isIntegralPerfectoid hR ρ hρ)

/-- 根付き単項商の任意の普遍perfectoid化は全射。 -/
theorem surjective_of_isPerfectoidization_of_compatibleRoots_unconditional
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {C : Type u} [CommRing C] (f : R ⧸ Ideal.span {ρ 0} →+* C)
    (hf : IsPerfectoidization p f) : Function.Surjective f :=
  surjective_of_isPerfectoidization_of_compatibleRoots hR ρ hρ
    (compatibleRootCompletion_isIntegralPerfectoid hR ρ hρ) f hf

end SerrePositivity.BhattScholze
