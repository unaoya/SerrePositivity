module

public import SerrePositivity.CommutativeAlgebra.AdicTermEuler
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel

/-!
# The adic term Euler sum of a Koszul complex

Successive scalar cones turn the adic term Euler sum into the corresponding
iterated Samuel difference. For a system of parameters this difference is eventually
the multiplicity, by the Samuel dimension theorem and the polynomial difference formula.
This computation uses no Koszul multiplicity formula as an input.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KoszulAdicEuler

open CategoryTheory CategoryTheory.Limits IsLocalRing Filter PolynomialFiniteDifference

variable {R : Type u} [CommRing R]

/-- The empty Koszul complex has just the base module's Samuel length as its term Euler sum. -/
theorem euler_koszul_zero (z : Fin 0 → R) (I : Ideal R) (n : ℤ) :
    AdicTermEuler.euler (koszulComplex z) I n =
      ((HilbertSamuel.samuelFunction R I R n.toNat).toNat : ℝ) := by
  unfold AdicTermEuler.euler
  rw [finsum_eq_single _ (0 : ℤ)]
  · rw [Int.negOnePow_zero, Units.val_one, Int.cast_one, one_mul]
    unfold AdicTermEuler.termLength
    rw [add_zero]
    have e : (koszulComplex z).X 0 ≃ₗ[R] R :=
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).toLinearEquiv
    rw [HilbertSamuel.samuelFunction_eq_of_linearEquiv I e]
  · intro q hq
    have hzero : IsZero ((koszulComplex z).X q) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of R R) q hq
    rw [AdicTermEuler.termLength_eq_zero_of_isZero _ _ _ _ hzero, mul_zero]

/-- The Koszul complex supplies the finite term bounds needed in the cone recursion. -/
theorem koszul_bounded {h : ℕ} (z : Fin h → R) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((koszulComplex z).X q) :=
  ⟨-(h : ℤ), 0, fun q hq => hq.elim
    (koszulComplex_isZero_X_of_lt z q) (koszulComplex_isZero_X_of_pos z q)⟩

variable [IsNoetherianRing R] [IsLocalRing R]

/-- The `h`-generator Koszul term Euler sum is the `h`th Samuel difference.
The bound on `n` handles the truncation in natural-number subtraction. -/
theorem euler_koszul_eq_backwardDifference {h : ℕ} (z : Fin h → R)
    (I : Ideal R) (hI : I.radical = maximalIdeal R) (n : ℕ) (hn : h ≤ n) :
    AdicTermEuler.euler (koszulComplex z) I (n : ℤ) =
      ((backwardDifferenceSeq^[h]
        (fun m => ((HilbertSamuel.samuelFunction R I R m).toNat : ℚ))) n : ℝ) := by
  induction h generalizing n with
  | zero =>
    rw [euler_koszul_zero, Int.toNat_natCast, Function.iterate_zero_apply]
    simp only [Rat.cast_natCast]
  | succ h ih =>
    let P := koszulComplex (Fin.init z)
    have hfinite : ∀ q, Module.Finite R (P.X q) :=
      fun q => (koszulComplex_free_finite_X (Fin.init z) q).2
    have hbounded := koszul_bounded (Fin.init z)
    rw [koszulComplex_succ,
      AdicTermEuler.euler_cone _ I hI (n : ℤ) hfinite hfinite hbounded hbounded,
      ih (Fin.init z) n (by omega)]
    have hnat : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
    rw [hnat, ih (Fin.init z) (n - 1) (by omega), Function.iterate_succ_apply',
      backwardDifferenceSeq, Rat.cast_sub]

/-- For a system of parameters, the adic term Euler sum is eventually its multiplicity. -/
theorem eventually_euler_koszul_eq_multiplicity {h : ℕ} (z : Fin h → R)
    (hz : IsSystemOfParameters R z) :
    ∀ᶠ n : ℕ in atTop,
      AdicTermEuler.euler (koszulComplex z) (Ideal.span (Set.range z)) (n : ℤ) =
        (HilbertSamuel.multiplicity R (Ideal.span (Set.range z)) R : ℝ) := by
  let I := Ideal.span (Set.range z)
  let P := HilbertSamuel.poly R I R
  have hI : I.radical = maximalIdeal R := hz.2
  have hd : dimToNat (ringKrullDim R) = h := by rw [hz.1]; simp [dimToNat]
  have hp := HilbertSamuel.isSamuelPoly_poly_of_radical R I hI R
  have hpval : ∀ᶠ n : ℕ in atTop,
      ((HilbertSamuel.samuelFunction R I R n).toNat : ℚ) = P.eval (n : ℚ) := by
    filter_upwards [hp] with n hn
    exact hn.2
  have hdegree : P.natDegree ≤ h :=
    ((HilbertSamuel.natDegree_poly_eq_dim R I hI).trans hd).le
  have hdiff := eventually_iterate_backwardDifferenceSeq_eq_coeff hpval h hdegree
  have hmult : HilbertSamuel.multiplicity R I R = (h.factorial : ℚ) * P.coeff h := by
    dsimp only [HilbertSamuel.multiplicity]
    rw [Module.supportDim_self_eq_ringKrullDim, hd]
  filter_upwards [hdiff, eventually_ge_atTop h] with n hn hnh
  rw [euler_koszul_eq_backwardDifference z I hI n hnh, hn, hmult]

end SerrePositivity.KoszulAdicEuler
