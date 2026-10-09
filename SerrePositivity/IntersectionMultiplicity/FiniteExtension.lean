module

public import SerrePositivity.EulerChar
public import Mathlib.LinearAlgebra.Quotient.Defs
public import SerrePositivity.Inputs.IntersectionTheory
public import SerrePositivity.IntersectionMultiplicity.LocalAlgebra

/-!
# Rank factors in intersection multiplicity

This file is independent of Galois actions, Lemma 3.5 and normalized length.
The formal rank calculation is separated from its inputs: additivity on an
exact sequence, the value on finite direct sums, and vanishing on the torsion
cokernel. Those inputs will be supplied by general intersection-multiplicity
lemmas and the Roberts--Gillet--Soulé vanishing theorem.
-/

public section

universe u

namespace SerrePositivity

variable {R : Type u} [CommRing R]
variable {D D' E E' : Type u}
  [AddCommGroup D] [Module R D] [AddCommGroup D'] [Module R D']
  [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']

/-- Additivity and vanishing discard the cokernel of a generic-basis map
in the first variable. The direct-sum evaluation supplies the rank factor. -/
theorem chi_rank_factor_left_of_additivity_and_vanishing (a : ℕ)
    (f : (Fin a → D) →ₗ[R] D')
    (hadd : chi R D' E = chi R (Fin a → D) E + chi R (D' ⧸ LinearMap.range f) E)
    (hfree : chi R (Fin a → D) E = (a : ℤ) * chi R D E)
    (hvanish : chi R (D' ⧸ LinearMap.range f) E = 0) :
    chi R D' E = (a : ℤ) * chi R D E := by
  rw [hadd, hfree, hvanish, add_zero]

/-- The same rank calculation in the second variable. No Tor symmetry is used. -/
theorem chi_rank_factor_right_of_additivity_and_vanishing (a : ℕ)
    (f : (Fin a → E) →ₗ[R] E')
    (hadd : chi R D E' = chi R D (Fin a → E) + chi R D (E' ⧸ LinearMap.range f))
    (hfree : chi R D (Fin a → E) = (a : ℤ) * chi R D E)
    (hvanish : chi R D (E' ⧸ LinearMap.range f) = 0) :
    chi R D E' = (a : ℤ) * chi R D E := by
  rw [hadd, hfree, hvanish, add_zero]

/-- Combine the two independent rank comparisons. -/
theorem chi_rank_factors (aD aE : ℕ)
    (hD : chi R D' E' = (aD : ℤ) * chi R D E')
    (hE : chi R D E' = (aE : ℤ) * chi R D E) :
    chi R D' E' = (aD : ℤ) * aE * chi R D E := by
  rw [hD, hE, mul_assoc]

/-- Adding a finite natural dimension preserves a strict dimension inequality. -/
lemma dimension_add_nat_lt {x : WithBot ℕ∞} {a b : ℕ}
    (hx : x < (a : WithBot ℕ∞)) : x + (b : WithBot ℕ∞) < ((a + b : ℕ) : WithBot ℕ∞) := by
  cases x with
  | bot => simp
  | coe x =>
    have h : x < (a : ℕ∞) := by exact_mod_cast hx
    have h' := (ENat.add_lt_add_iff_right (ENat.natCast_ne_top b)).mpr h
    exact_mod_cast h'

section extension

variable [IsRegularLocalRing R] [Inputs.IntersectionAdditivity R]
  [Inputs.FiniteModuleGeometry R] [Inputs.IntersectionVanishing R]

/-- Finite extensions contribute their generic ranks. The proof constructs
generic-basis injections, uses vanishing for the lower-dimensional cokernels,
and applies additivity in each variable separately. No Galois data is used. -/
theorem chi_finite_extensions
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (T U : Type u) [CommRing T] [Algebra R T] [Algebra (R ⧸ P) T]
    [IsScalarTower R (R ⧸ P) T] [Module.Finite R T] [Module.Finite (R ⧸ P) T]
    [CommRing U] [Algebra R U] [Algebra (R ⧸ Q) U]
    [IsScalarTower R (R ⧸ Q) U] [Module.Finite R U] [Module.Finite (R ⧸ Q) U]
    (hT : 0 < Module.finrank (R ⧸ P) T) (hU : 0 < Module.finrank (R ⧸ Q) U)
    (hprimary : (P ⊔ Q).radical = IsLocalRing.maximalIdeal R)
    (h l : ℕ) (hP : ringKrullDim (R ⧸ P) = h) (hQ : ringKrullDim (R ⧸ Q) = l)
    (hsum : ((h + l : ℕ) : WithBot ℕ∞) = ringKrullDim R) :
    chi R T U = (Module.finrank (R ⧸ P) T : ℤ) * Module.finrank (R ⧸ Q) U *
      chi R (R ⧸ P) (R ⧸ Q) := by
  have annT := quotient_action_annihilator P T
  have annU := quotient_action_annihilator Q U
  have annD := quotient_action_annihilator P (R ⧸ P)
  have annE := quotient_action_annihilator Q (R ⧸ Q)
  have finTU := Inputs.FiniteModuleGeometry.tensor_finite P Q T U annT annU hprimary
  have finDU := Inputs.FiniteModuleGeometry.tensor_finite P Q (R ⧸ P) U annD annU hprimary
  have finDE := Inputs.FiniteModuleGeometry.tensor_finite P Q (R ⧸ P) (R ⧸ Q) annD annE hprimary
  obtain ⟨f, hf, hC⟩ := Inputs.FiniteModuleGeometry.generic_basis P T hT
  obtain ⟨g, hg, hK⟩ := Inputs.FiniteModuleGeometry.generic_basis Q U hU
  have finCU := Inputs.FiniteModuleGeometry.tensor_finite P Q (T ⧸ LinearMap.range f) U
    (annT.trans (annihilator_le_quotient T _)) annU hprimary
  have finDK := Inputs.FiniteModuleGeometry.tensor_finite P Q (R ⧸ P) (U ⧸ LinearMap.range g)
    annD (annU.trans (annihilator_le_quotient U _)) hprimary
  have dimU : Module.supportDim R U = (l : WithBot ℕ∞) := by
    rw [Inputs.FiniteModuleGeometry.supportDim_of_rank_pos Q U hU, hQ]
  have dimD : Module.supportDim R (R ⧸ P) = (h : WithBot ℕ∞) := by
    rw [Module.supportDim_quotient_eq_ringKrullDim, hP]
  have vanishC : chi R (T ⧸ LinearMap.range f) U = 0 :=
    Inputs.IntersectionVanishing.vanish _ _ finCU (by
      rw [dimU, ← hsum]
      exact dimension_add_nat_lt (hP ▸ hC))
  have vanishK : chi R (R ⧸ P) (U ⧸ LinearMap.range g) = 0 :=
    Inputs.IntersectionVanishing.vanish _ _ finDK (by
      rw [dimD, add_comm, ← hsum, Nat.add_comm h l]
      exact dimension_add_nat_lt (hQ ▸ hK))
  have left := chi_rank_factor_left_of_additivity_and_vanishing
    (Module.finrank (R ⧸ P) T) f
    (Inputs.IntersectionAdditivity.add_left _ _ _ _ f (LinearMap.range f).mkQ hf
      (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f) finTU)
    (Inputs.IntersectionAdditivity.pi_left _ _ finDU _) vanishC
  have right := chi_rank_factor_right_of_additivity_and_vanishing
    (Module.finrank (R ⧸ Q) U) g
    (Inputs.IntersectionAdditivity.add_right _ _ _ _ g (LinearMap.range g).mkQ hg
      (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range g) finDU)
    (Inputs.IntersectionAdditivity.pi_right _ _ finDE _) vanishK
  exact chi_rank_factors _ _ left right

end extension

end SerrePositivity
