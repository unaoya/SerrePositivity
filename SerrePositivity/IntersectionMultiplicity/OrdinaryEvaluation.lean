module

public import SerrePositivity.Inputs.IntersectionTheory
public import SerrePositivity.CommutativeAlgebra.LengthComparison

/-! # Ordinary evaluation of a resolution after coefficient extension -/

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
      have hz : IsZero (K.homology i) := (K.sc i).isZero_homology_of_isZero_X₂
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

end SerrePositivity
