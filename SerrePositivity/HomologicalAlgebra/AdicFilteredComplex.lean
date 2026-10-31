module

public import SerrePositivity.HomologicalAlgebra.ModuleSubcomplex
public import SerrePositivity.HomologicalAlgebra.Complex.Basic

/-! # The shifted adic filtration of a complex

For a differential with image in `I` times the next term, the submodules
`I^max(n+q,0) P^q` form a subcomplex. 商の有限長性は `CommutativeAlgebra.AdicFilteredLength` で別に供給する。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AdicFilteredComplex

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R)

def term (n q : ℤ) : Submodule R (P.X q) := I ^ (n + q).toNat • ⊤

/-- A matrix whose entries are in `I` raises every adic power by one. -/
lemma map_pow_smul_top_le {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : f.range ≤ I • ⊤) (k : ℕ) :
    (I ^ k • ⊤ : Submodule R M).map f ≤ I ^ (k + 1) • ⊤ := by
  rw [Submodule.map_smul'', Submodule.map_top, pow_succ, mul_smul]
  exact Submodule.smul_mono le_rfl hf

variable (hd : ∀ q, (P.d q (q + 1)).hom.range ≤ I • ⊤)

include hd in
lemma stable (n i j : ℤ) (x : P.X i) (hx : x ∈ term P I n i) :
    P.d i j x ∈ term P I n j := by
  by_cases hij : (ComplexShape.up ℤ).Rel i j
  · change i + 1 = j at hij
    subst j
    by_cases hn : 0 ≤ n + i
    · have hnat : (n + (i + 1)).toNat = (n + i).toNat + 1 := by omega
      change P.d i (i + 1) x ∈ I ^ (n + (i + 1)).toNat • ⊤
      rw [hnat]
      exact map_pow_smul_top_le I (P.d i (i + 1)).hom (hd i) (n + i).toNat
        (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
    · have hz : (n + (i + 1)).toNat = 0 := by omega
      simp [term, hz]
  · rw [P.shape i j hij]
    exact Submodule.zero_mem _

def tail (n : ℤ) := ModuleSubcomplex.subcomplex P (term P I n) (stable P I hd n)

def quotient (n : ℤ) := ModuleSubcomplex.quotient P (term P I n) (stable P I hd n)

def projection (n : ℤ) : P ⟶ quotient P I hd n :=
  ModuleSubcomplex.projection P (term P I n) (stable P I hd n)

theorem quasiIso_projection (n : ℤ) (hacyclic : ∀ q, IsZero ((tail P I hd n).homology q)) :
    QuasiIso (projection P I hd n) :=
  ModuleSubcomplex.quasiIso_projection P (term P I n) (stable P I hd n) hacyclic


end SerrePositivity.AdicFilteredComplex
