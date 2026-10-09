module

public import SerrePositivity.Inputs.IntersectionTheory
public import SerrePositivity.PerfectComplex.HomologySupport
public import SerrePositivity.PerfectComplex.Closure
public import SerrePositivity.CommutativeAlgebra.LengthComparison

/-!
# Base change of a finite free resolution to a finite local algebra

Let `R` be a regular local ring with the standard inputs
`Inputs.RegularHomologicalAlgebra R`, `T` a local ring finite over `R`, `M` a finite
`R`-module and `F` a finite free resolution of `M` (as a ℤ-indexed cochain complex).
Write `L = F ⊗_R T` for the base change.

- `chiOrd_baseChange_resolution`: over a common residue field, the ordinary Euler
  evaluation of `L` is the intersection characteristic `χ^R(T, M)`.
- `isPerfectSupported_baseChange_resolution`: if `T ⊗_R M` has finite length, `L` is a
  perfect complex supported at the closed point of `T`, in the form required by Lemma 3.5.
  The homological-to-homotopical bridge is `PerfectComplex/HomologySupport.lean`.

Neither statement uses Lemma 3.5, normalized lengths or Tor symmetry.
-/

public section

universe u

open CategoryTheory Limits IsLocalRing TensorProduct

namespace SerrePositivity

variable {R T : Type u} [CommRing R] [IsRegularLocalRing R]
  [Inputs.RegularHomologicalAlgebra R] [CommRing T] [IsLocalRing T] [Algebra R T]
  [Module.Finite R T]

omit [IsRegularLocalRing R] [Module.Finite R T] in
/-- Over a common residue field, a base-changed resolution has ordinary Euler
evaluation equal to the original intersection characteristic. -/
theorem chiOrd_baseChange_resolution
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsResolutionOf F (ModuleCat.of R M))
    (hres : Function.Surjective ((residue T).comp (algebraMap R T))) :
    chiOrd (baseChange (algebraMap R T) F) = (chi R T M : ℝ) := by
  let K := baseChange (algebraMap R T) F
  have hlen (i : ℕ) : Module.length T (K.homology (-(i : ℤ))) = torLength R i T M := by
    obtain ⟨e⟩ := Inputs.RegularHomologicalAlgebra.ordinaryTorIso T M F hF i
    exact (length_restrictScalars_eq hres _).symm.trans e.length_eq
  let f := fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * ((Module.length T (K.homology i)).toNat : ℝ)
  let g := fun i : ℕ ↦ -(i : ℤ)
  have hg : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    exact_mod_cast neg_injective hij
  have hs : Function.support f ⊆ Set.range g := by
    intro i hi
    have hn : i ≤ 0 := by
      by_contra h
      have hz : IsZero (K.homology i) := isZero_homology_of_isZero_X _ _
        (baseChange_isZero_X_of_pos (algebraMap R T) F hF.isZero_X i (by omega))
      have := ModuleCat.subsingleton_of_isZero hz
      exact hi (by simp [f, Module.length_eq_zero])
    exact ⟨(-i).toNat, by dsimp [g]; rw [Int.toNat_of_nonneg (by omega), neg_neg]⟩
  have hfull : (∑ᶠ i ∈ Set.range g, f i) = ∑ᶠ i : ℤ, f i := by
    rw [← finsum_mem_inter_support f (Set.range g), Set.inter_eq_right.mpr hs, finsum_mem_support]
  change (∑ᶠ i : ℤ, f i) = _
  rw [← hfull, finsum_mem_range hg]
  unfold chi
  have hcast : (((∑ᶠ i : ℕ, (-1 : ℤ) ^ i * ((torLength R i T M).toNat : ℤ)) : ℤ) : ℝ) =
      ∑ᶠ i : ℕ, ((((-1 : ℤ) ^ i * ((torLength R i T M).toNat : ℤ)) : ℤ) : ℝ) := by
    exact (Int.castRingHom ℝ).toAddMonoidHom.map_finsum_of_injective Int.cast_injective
      (fun i : ℕ ↦ (-1 : ℤ) ^ i * ((torLength R i T M).toNat : ℤ))
  rw [hcast]
  congr 1
  funext i
  simp only [f, g, Int.negOnePow_neg, Int.cast_negOnePow_natCast, hlen, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]

/-- A finite-length intersection gives the exact supported-perfect-complex
condition used by the norm comparison. -/
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
  have boundedL : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (L.X i) :=
    baseChange_bounded (algebraMap R T) F hbound
  have finiteH : ∀ i : ℤ, IsFiniteLength T (L.homology i) := by
    intro i
    by_cases hi : 0 < i
    · have hz : IsZero (L.homology i) := isZero_homology_of_isZero_X _ _
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
