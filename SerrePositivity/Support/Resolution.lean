module

public import SerrePositivity.Support.NullHomotopy
public import SerrePositivity.Inputs.IntersectionTheory
public import SerrePositivity.CommutativeAlgebra.LengthComparison

/-! # Closed-point support of a base-changed finite free resolution -/

public section

universe u

open CategoryTheory Limits IsLocalRing TensorProduct

namespace SerrePositivity

variable {R T : Type u} [CommRing R] [IsRegularLocalRing R]
  [Inputs.RegularHomologicalAlgebra R] [CommRing T] [IsLocalRing T] [Algebra R T]
  [Module.Finite R T]

/-- A finite-length intersection gives the exact supported-perfect-complex
condition used by the norm comparison. The homological-to-homotopical bridge
is proved in `Support/NullHomotopy.lean`. -/
theorem isPerfectSupported_baseChange_resolution
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsResolutionOf F (ModuleCat.of R M))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (F.X i))
    (hfree : ∀ i, Module.Free R (F.X i)) (hfinite : ∀ i, Module.Finite R (F.X i))
    (htensor : Module.length R (T ⊗[R] M) ≠ ⊤)
    {e : ℕ} (w : Fin e → T) (hw : (Ideal.span (Set.range w)).radical = maximalIdeal T) :
    IsPerfectSupported w (baseChange (algebraMap R T) F) := by
  have : IsNoetherianRing T := IsNoetherianRing.of_finite R T
  let L := baseChange (algebraMap R T) F
  have finiteX : ∀ i, Module.Finite T (L.X i) := by
    intro i
    have := hfinite i
    exact finite_baseChange (algebraMap R T) (F.X i)
  have freeX : ∀ i, Module.Free T (L.X i) := by
    intro i
    have := hfree i
    exact free_baseChange (algebraMap R T) (F.X i)
  have boundedL : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (L.X i) := by
    obtain ⟨a, b, hab⟩ := hbound
    exact ⟨a, b, fun i hi ↦ (ModuleCat.extendScalars (algebraMap R T)).map_isZero (hab i hi)⟩
  have finiteH : ∀ i : ℤ, IsFiniteLength T (L.homology i) := by
    intro i
    by_cases hi : 0 < i
    · have hz : IsZero (L.homology i) := (L.sc i).isZero_homology_of_isZero_X₂
        (baseChange_isZero_X_of_pos (algebraMap R T) F hF.isZero_X i hi)
      have := ModuleCat.subsingleton_of_isZero hz
      exact IsFiniteLength.of_subsingleton
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) :=
        ⟨(-i).toNat, by rw [Int.toNat_of_nonneg (by omega), neg_neg]⟩
      obtain ⟨e⟩ := Inputs.RegularHomologicalAlgebra.ordinaryTorIso T M F hF n
      have ht := Inputs.RegularHomologicalAlgebra.finiteTor T M htensor n
      exact finiteLength_of_restrictScalars (L.homology (-(n : ℤ)))
        (Module.length_ne_top_iff.mp (ne_of_eq_of_ne e.length_eq ht))
  have supported : HasHomologySupport (Ideal.span (Set.range w)) L := by
    apply (homologySupport_iff_le_radical_annihilator _ L finiteX).mpr
    intro i
    obtain ⟨n, hn⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow (finiteH i)
    have hpow : (maximalIdeal T) ^ n ≤ Module.annihilator T (L.homology i) := by
      rwa [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe] at hn
    have hm : maximalIdeal T ≤ (Module.annihilator T (L.homology i)).radical := by
      intro x hx
      exact ⟨n, hpow (Ideal.pow_mem_pow hx n)⟩
    exact ((Ideal.span (Set.range w)).le_radical.trans_eq hw).trans hm
  exact isPerfectSupported_of_homologySupport w L finiteX freeX boundedL supported

end SerrePositivity
