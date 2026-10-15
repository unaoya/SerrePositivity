module

public import SerrePositivity.CommutativeAlgebra.FiniteLengthValue

public import SerrePositivity.PerfectComplex.Basic
public import SerrePositivity.CategoryTheory.AlternatingSum
public import SerrePositivity.CategoryTheory.FiniteSupportBounds
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Euler–Poincaré for bounded finite-length complexes

For a bounded complex whose terms have finite length, the alternating length of
homology equals the alternating length of the terms. The two exact sequences for
cycles and boundaries supply the degreewise identity, and adjacent boundary
contributions cancel in the alternating sum. Quasi-isomorphisms preserve ordinary
Euler characteristics without boundedness assumptions.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.FiniteLengthComplexEuler

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Kernel and image lengths add to the length of a module. -/
theorem length_ker_add_range {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Module.length R M = Module.length R f.ker + Module.length R f.range := by
  have h := Module.length_eq_add_of_exact f.ker.subtype f.ker.mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ f.ker)
  rwa [f.quotKerEquivRange.length_eq] at h

/-- The range inside cycles has the same length as the original incoming image. -/
theorem length_toCycles_range (S : ShortComplex (ModuleCat.{u} R)) :
    Module.length R S.moduleCatToCycles.range = Module.length R S.f.hom.range := by
  have h := S.moduleCatToCycles.quotKerEquivRange.length_eq
  have hk : S.moduleCatToCycles.ker = S.f.hom.ker := by
    ext x
    change S.moduleCatToCycles x = 0 ↔ S.f.hom x = 0
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  rw [hk, S.f.hom.quotKerEquivRange.length_eq] at h
  exact h.symm

/-- The middle length is homology length plus the two boundary image lengths. -/
theorem shortComplex_length_identity (S : ShortComplex (ModuleCat.{u} R))
    (hfinite : IsFiniteLength R S.X₂) :
    ((Module.length R S.X₂).toNat : ℝ) =
      ((Module.length R S.f.hom.range).toNat : ℝ) +
      ((Module.length R S.homology).toNat : ℝ) +
      ((Module.length R S.g.hom.range).toNat : ℝ) := by
  have hcy := lengthNat_add_of_exact S.moduleCatToCycles.range.subtype
    S.moduleCatToCycles.range.mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    (hfinite.of_injective S.g.hom.ker.injective_subtype)
  have hX := lengthNat_ker_add_range S.g.hom hfinite
  have hh := S.moduleCatHomologyIso.toLinearEquiv.length_eq
  change Module.length R S.homology =
    Module.length R (S.g.hom.ker ⧸ S.moduleCatToCycles.range) at hh
  rw [hcy, length_toCycles_range, ← hh] at hX
  exact_mod_cast hX

/-- Ordinary Euler characteristic is invariant under a quasi-isomorphism. -/
theorem chiOrd_eq_of_quasiIso {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) [QuasiIso f] : chiOrd P = chiOrd Q := by
  unfold chiOrd
  congr 1
  funext q
  rw [(isoOfQuasiIsoAt f q).toLinearEquiv.length_eq]

/-- A categorical zero module has length zero. -/
theorem length_eq_zero_of_isZero (M : ModuleCat.{u} R) (hM : IsZero M) :
    Module.length R M = 0 := by
  let : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hM
  exact Module.length_eq_zero

/-- A numerical function that vanishes outside an integer interval has finite support. -/
theorem finiteSupport_of_bounded_zero (f : ℤ → ℝ) (a b : ℤ)
    (hf : ∀ q, q < a ∨ b < q → f q = 0) : Function.HasFiniteSupport f :=
  SerrePositivity.finiteSupport_of_bounded_zero f a b hf

/-- Euler–Poincaré: the alternating homology length of a bounded finite-length
complex is the alternating length of its terms. -/
theorem chiOrd_eq_alternating_term_lengths
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (hfinite : ∀ q, IsFiniteLength R (P.X q)) :
    chiOrd P = ∑ᶠ q : ℤ,
      ((q.negOnePow : ℤ) : ℝ) * ((Module.length R (P.X q)).toNat : ℝ) := by
  obtain ⟨a, b, hab⟩ := hbounded
  let boundary := fun q : ℤ =>
    ((Module.length R (P.d q (q + 1)).hom.range).toNat : ℝ)
  let homology := fun q : ℤ => ((Module.length R (P.homology q)).toNat : ℝ)
  have hidentity (q : ℤ) : ((Module.length R (P.X q)).toNat : ℝ) =
      boundary (q - 1) + homology q + boundary q := by
    have h := shortComplex_length_identity (P.sc q) (hfinite q)
    change ((Module.length R (P.X q)).toNat : ℝ) =
      ((Module.length R (P.d ((ComplexShape.up ℤ).prev q) q).hom.range).toNat : ℝ) +
      ((Module.length R (P.homology q)).toNat : ℝ) +
      ((Module.length R (P.d q ((ComplexShape.up ℤ).next q)).hom.range).toNat : ℝ) at h
    rw [CochainComplex.prev, CochainComplex.next] at h
    dsimp only [boundary, homology]
    rw [show q - 1 + 1 = q by omega]
    exact h
  have hbfin : Function.HasFiniteSupport boundary := by
    apply finiteSupport_of_bounded_zero boundary a b
    intro q hq
    have hzero := length_eq_zero_of_isZero (P.X q) (hab q hq)
    have hle := Module.length_le_of_surjective (P.d q (q + 1)).hom.rangeRestrict
      (P.d q (q + 1)).hom.surjective_rangeRestrict
    rw [hzero] at hle
    have hz : Module.length R (P.d q (q + 1)).hom.range = 0 := le_antisymm hle bot_le
    simp only [boundary, hz, ENat.toNat_zero, Nat.cast_zero]
  have hhfin : Function.HasFiniteSupport homology := by
    apply finiteSupport_of_bounded_zero homology a b
    intro q hq
    have hz := length_eq_zero_of_isZero (P.homology q)
      (isZero_homology_of_isZero_X P q (hab q hq))
    simp only [homology, hz, ENat.toNat_zero, Nat.cast_zero]
  exact alternatingFinsum_eq_of_boundary
    (fun q ↦ ((Module.length R (P.X q)).toNat : ℝ)) homology boundary hbfin hhfin hidentity

end SerrePositivity.FiniteLengthComplexEuler
