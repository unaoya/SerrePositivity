module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Exact.Basic

/-! # Restriction of exact module maps to a submodule and its preimage and image -/

public section
namespace SerrePositivity
variable {R : Type*} [CommRing R]
  {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]

lemma submoduleRestriction_injective (U : Submodule R M₂) (f : M₁ →ₗ[R] M₂)
    (hf : Function.Injective f) :
    Function.Injective (f.restrict (p := U.comap f) (q := U) (fun _ h => h)) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

lemma submoduleImage_restrict_surjective (U : Submodule R M₂) (g : M₂ →ₗ[R] M₃) :
    Function.Surjective
      (g.restrict (p := U) (q := U.map g) (fun _ h => Submodule.mem_map_of_mem h)) := by
  rintro ⟨n, hn⟩
  obtain ⟨m, hm, he⟩ := Submodule.mem_map.mp hn
  exact ⟨⟨m, hm⟩, Subtype.ext he⟩

/-- No finite generation, Noetherian hypothesis, or surjectivity onto M₃ is needed. -/
lemma submoduleRestriction_exact (U : Submodule R M₂)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (he : Function.Exact f g) :
    Function.Exact (f.restrict (p := U.comap f) (q := U) (fun _ h => h))
      (g.restrict (p := U) (q := U.map g) (fun _ h => Submodule.mem_map_of_mem h)) := by
  intro n
  constructor
  · intro hn
    have hn' : g (n : M₂) = 0 := congrArg Subtype.val hn
    obtain ⟨m, hm⟩ := (he (n : M₂)).mp hn'
    exact ⟨⟨m, by change f m ∈ U; rw [hm]; exact n.property⟩, Subtype.ext hm⟩
  · rintro ⟨m, rfl⟩
    apply Subtype.ext
    exact he.apply_apply_eq_zero m

end SerrePositivity
