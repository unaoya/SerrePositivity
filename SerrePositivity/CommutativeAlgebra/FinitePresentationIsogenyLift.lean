module

public import Mathlib.Algebra.Module.FinitePresentation
public import SerrePositivity.CommutativeAlgebra.LocalizationPowerBound

/-! # 有限表示加群からの局所化同型の分母払い

元の同型の一つの共通分母を払い、元の加群上の写像を構成する。
Noether 性、正則性、終域の有限性を要求しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity
variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.FinitePresentation R M]

/-- 局所化同型の共通分母を払い、局所化すると全単射となる元の加群写像を得る。 -/
theorem exists_away_comparison_of_finitePresentation (g : R)
    (e : LocalizedModule (Submonoid.powers g) M ≃ₗ[R]
      LocalizedModule (Submonoid.powers g) N) :
    ∃ (k : ℕ) (f : M →ₗ[R] N),
      awayModuleMap g f = g ^ k • e.toLinearMap ∧ Function.Bijective (awayModuleMap g f) := by
  let S := Submonoid.powers g
  let ιM := LocalizedModule.mkLinearMap S M
  let ιN := LocalizedModule.mkLinearMap S N
  obtain ⟨f, s, hf⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S ιN
    (e.toLinearMap.comp ιM)
  have hmap : awayModuleMap g f = (s : R) • e.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S ιM ιN
    change (IsLocalizedModule.map S ιM ιN f).comp ιM =
      ((s : R) • e.toLinearMap).comp ιM
    rw [IsLocalizedModule.map_comp]
    simpa only [Submonoid.smul_def, LinearMap.smul_comp] using hf
  obtain ⟨k, hk⟩ := s.property
  refine ⟨k, f, ?_, ?_⟩
  · simpa only [hk] using hmap
  · rw [hmap]
    exact ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units ιN s)).comp e.bijective

end SerrePositivity
