module

public import SerrePositivity.CommutativeAlgebra.AdicModuleProduct
public import SerrePositivity.CommutativeAlgebra.SamuelModuleProperties
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.PolynomialFiniteDifference
public import SerrePositivity.CategoryTheory.AlternatingSum
public import Mathlib.Algebra.FiniteSupport.Basic

/-! # Euler sums of the finite adic quotients of Koszul terms

The cone decomposition gives a backward difference in the filtration index.
Iterating it computes the term Euler sum as the corresponding Samuel difference.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AdicTermEuler

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]

def termLength (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R) (n q : ℤ) : ℝ :=
  ((HilbertSamuel.samuelFunction R I (P.X q) (n + q).toNat).toNat : ℝ)

def euler (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R) (n : ℤ) : ℝ :=
  ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * termLength P I n q

lemma termLength_eq_zero_of_isZero (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (I : Ideal R) (n q : ℤ) (hq : IsZero (P.X q)) : termLength P I n q = 0 := by
  let : Subsingleton (P.X q) := ModuleCat.isZero_iff_subsingleton.mp hq
  simp [termLength, HilbertSamuel.samuelFunction, Module.length_eq_zero]

lemma finiteSupport_termLength (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (I : Ideal R) (n : ℤ)
    (hb : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q)) :
    Function.HasFiniteSupport (termLength P I n) := by
  obtain ⟨a, b, hab⟩ := hb
  apply (Set.finite_Icc a b).subset
  intro q hq
  by_contra hnot
  exact hq (termLength_eq_zero_of_isZero P I n q (hab q (by
    simp only [Set.mem_Icc] at hnot
    omega)))

lemma alternatingFinsum_add_one (f : ℤ → ℝ) :
    (∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * f (q + 1)) =
      -(∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * f q) := by
  calc
    _ = ∑ᶠ q : ℤ, (((q - 1).negOnePow : ℤ) : ℝ) * f q := by
      have h := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
        (f := fun q : ℤ => (((q - 1).negOnePow : ℤ) : ℝ) * f q)
      simpa using h
    _ = ∑ᶠ q : ℤ, -(((q.negOnePow : ℤ) : ℝ) * f q) := by
      congr 1
      funext q
      simp [sub_eq_add_neg, Int.negOnePow_add]
    _ = _ := finsum_neg_distrib _

variable [IsNoetherianRing R] [IsLocalRing R]

lemma termLength_cone {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (n q : ℤ)
    [Module.Finite R (P.X (q + 1))] [Module.Finite R (Q.X q)] :
    termLength (CochainComplex.mappingCone f) I n q =
      termLength P I (n - 1) (q + 1) + termLength Q I n q := by
  let e : (CochainComplex.mappingCone f).X q ≃ₗ[R] (P.X (q + 1) × Q.X q) :=
    ((HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl) ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv
  dsimp only [termLength]
  rw [show n - 1 + (q + 1) = n + q by ring,
    HilbertSamuel.samuelFunction_eq_of_linearEquiv I e,
    AdicModuleProduct.samuelFunction_prod,
    ENat.toNat_add
      (HilbertSamuel.samuelFunction_ne_top R I hI (P.X (q + 1)) _)
      (HilbertSamuel.samuelFunction_ne_top R I hI (Q.X q) _), Nat.cast_add]

/-- The Euler sum of the cone quotients is a difference in the adic index. -/
theorem euler_cone {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (n : ℤ)
    (hP : ∀ q, Module.Finite R (P.X q)) (hQ : ∀ q, Module.Finite R (Q.X q))
    (bP : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (bQ : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (Q.X q)) :
    euler (CochainComplex.mappingCone f) I n = euler Q I n - euler P I (n - 1) := by
  have hflP : Function.HasFiniteSupport (fun q => termLength P I (n - 1) (q + 1)) :=
    (finiteSupport_termLength P I (n - 1) bP).preimage
    (Equiv.addRight (1 : ℤ)).injective.injOn
  have hflQ := finiteSupport_termLength Q I n bQ
  have hwP : Function.HasFiniteSupport
      (fun q : ℤ => ((q.negOnePow : ℤ) : ℝ) * termLength P I (n - 1) (q + 1)) :=
    hflP.mul_right _
  have hwQ : Function.HasFiniteSupport
      (fun q : ℤ => ((q.negOnePow : ℤ) : ℝ) * termLength Q I n q) := hflQ.mul_right _
  have heq : (fun q : ℤ => ((q.negOnePow : ℤ) : ℝ) *
      termLength (CochainComplex.mappingCone f) I n q) =
      fun q => ((q.negOnePow : ℤ) : ℝ) * termLength P I (n - 1) (q + 1) +
        ((q.negOnePow : ℤ) : ℝ) * termLength Q I n q := by
    funext q
    let : Module.Finite R (P.X (q + 1)) := hP _
    let : Module.Finite R (Q.X q) := hQ _
    rw [termLength_cone f I hI, mul_add]
  unfold euler
  rw [heq, finsum_add_distrib hwP hwQ, alternatingFinsum_add_one]
  ring

end SerrePositivity.AdicTermEuler
