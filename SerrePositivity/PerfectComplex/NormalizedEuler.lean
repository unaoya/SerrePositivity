module

public import SerrePositivity.HomologicalAlgebra.ConeLES
public import SerrePositivity.PerfectComplex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Euler evaluation for an abstract additive length

`lambdaEuler lam P = Σ_i (-1)^i λ H^i(P)` for a normalized length `λ`. Finite normalized
homology lengths and power torsion suffice for homotopy invariance and mapping-cone
additivity. No Noetherian hypothesis on the coefficient ring is used.

The ordinary length is the normalized length `NormalizedLength.ordinary` for `J = ⊥`, so the
ordinary Euler evaluation `chiOrd` is the special case `chiOrd_eq_lambdaEuler_ordinary`; the
ordinary statements are derived from the ones here in `OrdinaryEuler.lean`.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped ENNReal

namespace SerrePositivity

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)

/-- Euler evaluation of a coefficient-ring complex by the abstract length. -/
noncomputable def lambdaEuler (P : CochainComplex (ModuleCat.{u} C) ℤ) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (P.homology i)).toReal

/-- Exactness expresses the length of the middle term as the sum of image lengths. -/
lemma lambdaLengthReal_eq_add_range {M N L : Type u} [AddCommGroup M] [Module C M]
    [AddCommGroup N] [Module C N] [AddCommGroup L] [Module C L]
    (f : M →ₗ[C] N) (g : N →ₗ[C] L) (hfg : Function.Exact f g)
    (tN : IsPowTorsion J N) (hN : lam.len N ≠ ⊤) :
    (lam.len N).toReal = (lam.len (LinearMap.range f)).toReal +
      (lam.len (LinearMap.range g)).toReal := by
  have hk : lam.len (LinearMap.ker g) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (lam.len_submodule_le tN _)
  have hr : lam.len (LinearMap.range g) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (lam.len_range_le g tN)
  rw [lam.len_eq_add_ker_range g tN, ENNReal.toReal_add hk hr,
    ← LinearMap.exact_iff.mp hfg]

/-- Boundedness makes the homology evaluation finitely supported. -/
lemma lambdaHomology_hasFiniteSupport (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    Function.HasFiniteSupport (fun i ↦ (lam.len (P.homology i)).toReal) := by
  obtain ⟨a, b, hab⟩ := hP
  apply (Set.finite_Icc a b).subset
  intro i hi
  by_contra hn
  have hzero : IsZero (P.homology i) :=
    (P.sc i).isZero_homology_of_isZero_X₂ (hab i (by simp only [Set.mem_Icc] at hn; omega))
  have := ModuleCat.subsingleton_of_isZero hzero
  exact hi (by simp [lam.len_eq_zero_of_subsingleton])

/-- Homotopy equivalent coefficient complexes have the same evaluation. -/
lemma lambdaEuler_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} C) ℤ}
    (h : HomotopyEquiv P Q) : lambdaEuler lam P = lambdaEuler lam Q := by
  unfold lambdaEuler
  congr 1
  funext i
  rw [lam.len_congr _ _ (h.toHomologyIso i).toLinearEquiv]

private lemma alternating_finsum_shift (f : ℤ → ℝ) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f (i - 1)) =
      -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f i) := by
  calc
    _ = ∑ᶠ i : ℤ, (((i + 1).negOnePow : ℤ) : ℝ) * f i := by
      have h := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
        (f := fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * f (i - 1))
      simpa using h.symm
    _ = ∑ᶠ i : ℤ, -(((i.negOnePow : ℤ) : ℝ) * f i) := by
      congr 1
      funext i
      simp [Int.negOnePow_add]
    _ = _ := finsum_neg_distrib _

set_option maxHeartbeats 800000 in
-- Transporting the three exact sequences with dependent homology objects
-- requires additional elaboration time.
/-- The Euler evaluation is additive on a mapping-cone triangle when
the homology is bounded, power torsion, and has finite length. -/
theorem lambdaEuler_cone {P Q : CochainComplex (ModuleCat.{u} C) ℤ} (f : P ⟶ Q)
    (hQ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (tP : ∀ i, IsPowTorsion J (P.homology i))
    (tQ : ∀ i, IsPowTorsion J (Q.homology i))
    (tC : ∀ i, IsPowTorsion J ((Cone.cone f).homology i))
    (lP : ∀ i, lam.len (P.homology i) ≠ ⊤)
    (lQ : ∀ i, lam.len (Q.homology i) ≠ ⊤)
    (lC : ∀ i, lam.len ((Cone.cone f).homology i) ≠ ⊤) :
    lambdaEuler lam (Cone.cone f) = lambdaEuler lam Q - lambdaEuler lam P := by
  let α := fun i ↦ (HomologicalComplex.homologyMap f i).hom
  let β := fun i ↦ (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) i).hom
  let δ := fun i ↦ (Cone.δ f i (i + 1) rfl).hom
  let a := fun i ↦ (lam.len (LinearMap.range (α i))).toReal
  let b := fun i ↦ (lam.len (LinearMap.range (β i))).toReal
  let d := fun i ↦ (lam.len (LinearMap.range (δ i))).toReal
  have ha : Function.HasFiniteSupport a := by
    apply (lambdaHomology_hasFiniteSupport lam Q hQ).subset
    intro i hi hz
    have hz' : lam.len (Q.homology i) = 0 := by
      have hn := lQ i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (α i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_submodule_le (tQ i) _) bot_le
    exact hi (by simp [a, this])
  have hb : Function.HasFiniteSupport b := by
    apply (lambdaHomology_hasFiniteSupport lam (Cone.cone f) hC).subset
    intro i hi hz
    have hz' : lam.len ((Cone.cone f).homology i) = 0 := by
      have hn := lC i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (β i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_submodule_le (tC i) _) bot_le
    exact hi (by simp [b, this])
  have hd : Function.HasFiniteSupport d := by
    apply (lambdaHomology_hasFiniteSupport lam (Cone.cone f) hC).subset
    intro i hi hz
    have hz' : lam.len ((Cone.cone f).homology i) = 0 := by
      have hn := lC i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (δ i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_range_le (δ i) (tC i)) bot_le
    exact hi (by simp [d, this])
  have hQlen : ∀ i, ((lam.len (Q.homology i)).toReal : ℝ) = a i + b i := fun i ↦
    lambdaLengthReal_eq_add_range lam (α i) (β i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₂ f i)) (tQ i) (lQ i)
  have hClen : ∀ i, ((lam.len ((Cone.cone f).homology i)).toReal : ℝ) = b i + d i := fun i ↦
    lambdaLengthReal_eq_add_range lam (β i) (δ i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₃ f i (i + 1) rfl)) (tC i) (lC i)
  have hPlen : ∀ i, ((lam.len (P.homology i)).toReal : ℝ) = d (i - 1) + a i := by
    intro i
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
    rw [add_sub_cancel_right]
    exact lambdaLengthReal_eq_add_range lam (δ j) (α (j + 1))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₁ f j (j + 1) rfl)) (tP (j + 1)) (lP (j + 1))
  have haw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * a i) :=
    ha.mul_right _
  have hbw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * b i) :=
    hb.mul_right _
  have hdw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * d i) :=
    hd.mul_right _
  have hds : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * d (i - 1)) := by
    have hdp : Function.HasFiniteSupport (fun i : ℤ ↦ d (i - 1)) :=
      hd.preimage (Equiv.subRight (1 : ℤ)).injective.injOn
    exact hdp.mul_right _
  have eQ : lambdaEuler lam Q = (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * b i) := by
    simp_rw [lambdaEuler, hQlen, mul_add]
    exact finsum_add_distrib haw hbw
  have eC : lambdaEuler lam (Cone.cone f) = (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * b i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * d i) := by
    simp_rw [lambdaEuler, hClen, mul_add]
    exact finsum_add_distrib hbw hdw
  have eP : lambdaEuler lam P = -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * d i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) := by
    simp_rw [lambdaEuler, hPlen, mul_add]
    rw [finsum_add_distrib hds haw, alternating_finsum_shift]
  rw [eC, eQ, eP]
  ring

/-! ## The ordinary length as a normalized length -/

/-- Casting `ℕ∞` into `ℝ≥0∞` and then into `ℝ` agrees with `ENat.toNat`; both send `⊤` to `0`. -/
lemma toReal_toENNReal (n : ℕ∞) : (n : ℝ≥0∞).toReal = (n.toNat : ℝ) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k => simp

/-- The ordinary Euler evaluation is the one for `NormalizedLength.ordinary`. -/
lemma chiOrd_eq_lambdaEuler_ordinary {T : Type u} [CommRing T]
    (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    chiOrd P = lambdaEuler (NormalizedLength.ordinary T) P := by
  unfold chiOrd lambdaEuler
  simp only [NormalizedLength.ordinary_len, toReal_toENNReal]

end SerrePositivity
