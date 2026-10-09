module

public import SerrePositivity.Paper.Lemma3_5
public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.Inputs.LengthAlgebra
public import SerrePositivity.IntersectionMultiplicity.LocalAlgebra

/-! # Applying Lemma 3.5 to a length algebra from Theorem 2.5 -/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

/-- Theorem 2.5 and the normalization-base data supply all normalized-length
hypotheses of Lemma 3.5. The length is restricted to base-maximal-ideal torsion
without changing any evaluation. -/
theorem normComparison_of_lengthAlgebra
    (A T C : Type u) [CommRing A] [IsLocalRing A] [CommRing T] [IsLocalRing T]
    [Algebra A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
    {e : ℕ} (z : Fin e → A) (hb : IsRegularNormalizationBase A T z)
    (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
    (hC : LengthAlgebraProps A T z C lam)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (htrans : IsGeometricallyTransitive A T G)
    (L : PerfSupp T (algebraMap A T ∘ z)) :
    (∀ (g : G) (i : ℤ), lam.len ((baseChange (algebraMap T C) (twist g L.1)).homology i) ≠ ⊤) ∧
      (∑ g : G, chiOrd (twist g L.1)) =
        ∑ g : G, chiLam lam (algebraMap T C) (twist g L.1) := by
  have : IsRegularLocalRing A := hb.regular
  have : Module.Finite A T := hb.finite
  obtain ⟨N, hN⟩ := maximalIdeal_pow_le_map_of_finite (R := A) T
  let lam' : NormalizedLength C ((maximalIdeal A).map (algebraMap A C)) :=
    lam.restrict _ (fun M _ _ hM ↦ IsPowTorsion.of_pow_le ⟨N, hN⟩ M hM)
  have heq (v : ℕ) :
      (fun j ↦ algebraMap T C ((algebraMap A T ∘ z) j ^ v)) =
        (fun j ↦ algebraMap A C (z j ^ v)) := by
    funext j
    simp [IsScalarTower.algebraMap_apply A T C]
  have hzero (v : ℕ) (hv : 0 < v) (i : ℕ) (hi : 0 < i) :
      lam'.len (koszulHomologySelf (fun j ↦ algebraMap A C (z j ^ v)) i) = 0 := by
    have h := hC.koszul_zero (algebraMap A T ∘ z) hb.sop v hv i hi
    rw [heq v] at h
    exact h
  have hquot (v : ℕ) (hv : 0 < v) :
      lam'.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (z j ^ v))) =
        ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞) := by
    have h := hC.base_eq v hv
    have ht : (fun j ↦ algebraMap T C (algebraMap A T (z j) ^ v)) =
        (fun j ↦ algebraMap A C (z j ^ v)) := heq v
    rw [ht] at h
    exact h
  have hfin : ∀ v j : ℕ,
      lam'.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤ := by
    intro v j
    by_cases hv : v = 0
    · subst v
      have hx : (fun k : Fin e ↦ algebraMap A C (z k ^ 0)) = (fun _ ↦ (1 : C)) := by
        funext k
        simp
      rw [hx]
      obtain ⟨v, hv⟩ := isSupported_koszulComplex (fun _ : Fin e ↦ (1 : C))
      obtain ⟨H⟩ := hv ⟨0, hb.pos⟩
      have h := H.homologyMap_eq (-(j : ℤ))
      simp only [one_pow, one_smul, HomologicalComplex.homologyMap_id,
        HomologicalComplex.homologyMap_zero] at h
      have hz := (IsZero.iff_id_eq_zero _).mpr h
      have := ModuleCat.subsingleton_of_isZero hz
      rw [lam'.len_eq_zero_of_subsingleton]
      exact ENNReal.zero_ne_top
    · have hv' : 0 < v := Nat.pos_of_ne_zero hv
      cases j with
      | zero =>
        have eq0 := lam'.len_congr _ _
          (koszulComplex_homology_zero_equiv (fun k ↦ algebraMap A C (z k ^ v))).some
        have hfQ := ne_of_eq_of_ne (hquot v hv') (ENNReal.natCast_ne_top _)
        exact ne_of_eq_of_ne eq0 hfQ
      | succ j =>
        rw [hzero v hv' (j + 1) (by omega)]
        exact ENNReal.zero_ne_top
  have ht1 : (fun j ↦ algebraMap A C (z j ^ 1)) = algebraMap A C ∘ z := by
    funext j
    simp
  have hkz : ∀ i : ℕ, 0 < i →
      lam'.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0 := by
    intro i hi
    have h := hzero 1 one_pos i hi
    rwa [ht1] at h
  have hq : lam'.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T := by
    have h := hquot 1 one_pos
    rw [ht1] at h
    simpa only [one_pow, one_mul] using h
  have h := lemma_3_5 hb.regular_params hb.dimA hkz hq hfin hb.residue_surjective
    p G hsurj htrans L
  exact ⟨h.2.1, h.2.2⟩

end SerrePositivity
