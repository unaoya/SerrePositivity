module

public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.CommutativeAlgebra.PowTorsion

/-!
# 有限長加群の Tor の冪ねじれ性

局所環上の有限長加群の Tor は、係数環に写した極大イデアルの冪で消える。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

variable [IsLocalRing A]

/-- `V` が有限長なら `Tor_i^A(C, V)` は `m_A C` の冪で消える。 -/
lemma torAlg_isPowTorsion (i : ℕ) (V : Type u) [AddCommGroup V] [Module A V]
    (hV : IsFiniteLength A V) : IsPowTorsion ((maximalIdeal A).map φ) (TorAlg φ i V) := by
  obtain ⟨n, hn⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hV
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, ← Ideal.map_pow, Ideal.map,
    SetLike.coe_subset_coe, Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, Module.mem_annihilator]
  intro x
  exact torAlg_smul_eq_zero φ i V a (fun v ↦ @hn v ⟨a, ha⟩) x

end SerrePositivity
