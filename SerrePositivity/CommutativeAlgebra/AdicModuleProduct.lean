module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuelBasic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # Ideal-power quotients of products of modules -/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AdicModuleProduct

variable {R M N : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem smul_top_prod (I : Ideal R) :
    (I • ⊤ : Submodule R (M × N)) =
      (I • ⊤ : Submodule R M).prod (I • ⊤ : Submodule R N) := by
  apply le_antisymm
  · intro x hx
    exact ⟨Submodule.smul_top_le_comap_smul_top I (LinearMap.fst R M N) hx,
      Submodule.smul_top_le_comap_smul_top I (LinearMap.snd R M N) hx⟩
  · intro x hx
    have h1 := Submodule.smul_top_le_comap_smul_top I (LinearMap.inl R M N) hx.1
    have h2 := Submodule.smul_top_le_comap_smul_top I (LinearMap.inr R M N) hx.2
    simpa using (I • (⊤ : Submodule R (M × N))).add_mem h1 h2

def quotientProdEquiv (I : Ideal R) :
    ((M × N) ⧸ (I • ⊤ : Submodule R (M × N))) ≃ₗ[R]
      (M ⧸ (I • ⊤ : Submodule R M)) × (N ⧸ (I • ⊤ : Submodule R N)) := by
  let f := (I • (⊤ : Submodule R M)).mkQ.prodMap (I • (⊤ : Submodule R N)).mkQ
  have hf : Function.Surjective f :=
    (I • (⊤ : Submodule R M)).mkQ_surjective.prodMap (I • (⊤ : Submodule R N)).mkQ_surjective
  have hker : f.ker = I • (⊤ : Submodule R (M × N)) := by
    rw [LinearMap.ker_prodMap, Submodule.ker_mkQ, Submodule.ker_mkQ, ← smul_top_prod]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)

theorem samuelFunction_prod (I : Ideal R) (n : ℕ) :
    HilbertSamuel.samuelFunction R I (M × N) n =
      HilbertSamuel.samuelFunction R I M n + HilbertSamuel.samuelFunction R I N n := by
  change Module.length R ((M × N) ⧸ (I ^ n • ⊤ : Submodule R (M × N))) = _
  rw [(quotientProdEquiv (M := M) (N := N) (I ^ n)).length_eq, Module.length_prod]
  rfl

end SerrePositivity.AdicModuleProduct
