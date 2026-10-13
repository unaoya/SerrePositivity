module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesMixedCompleteness

/-! # 有限変数冪級数環の極大イデアル

Mathlibの変数進完備化との同型を使って定数係数の核を計算する。
局所係数環では極大イデアルを係数の極大イデアルと全変数で生成する。
-/

public section
namespace SerrePositivity
open IsLocalRing

/-- 有限変数冪級数の定数係数写像の核は、全変数が生成するイデアル。 -/
theorem powerSeries_ker_constantCoeff (σ R : Type*) [Finite σ] [CommRing R] :
    RingHom.ker (MvPowerSeries.constantCoeff (σ := σ) (R := R)) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))) := by
  classical
  let P := MvPolynomial.idealOfVars σ R
  let e := (MvPowerSeries.toAdicCompletionAlgEquiv σ R).toRingEquiv
  have he : (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).map e =
      P.map (algebraMap (MvPolynomial σ R) (AdicCompletion P (MvPolynomial σ R))) := by
    change (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).map e =
      (Ideal.span (Set.range (MvPolynomial.X (σ := σ) (R := R)))).map
        (algebraMap (MvPolynomial σ R) (AdicCompletion P (MvPolynomial σ R)))
    simp_rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp [e, P, MvPolynomial.idealOfVars, AdicCompletion.algebraMap_apply,
      ← MvPolynomial.coe_X, MvPowerSeries.toAdicCompletion_coe]
  apply le_antisymm
  · intro f hf
    have hf0 : MvPowerSeries.constantCoeff f = 0 := hf
    have ht : MvPowerSeries.truncTotal 1 f = 0 := by
      ext d
      rw [MvPowerSeries.coeff_truncTotal_eq_ite]
      split_ifs with h
      · have hd : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
        subst d
        change MvPowerSeries.coeff 0 f = 0
        exact hf0
      · simp
    have hm : e f ∈ P.map (algebraMap (MvPolynomial σ R)
        (AdicCompletion P (MvPolynomial σ R))) := by
      rw [← AdicCompletion.ker_evalOneₐ_eq_map P (MvPolynomial.idealOfVars_fg σ R)]
      change AdicCompletion.evalOneₐ P (MvPowerSeries.toAdicCompletion σ R f) = 0
      have hz : (MvPowerSeries.toAdicCompletion σ R f).val 1 = 0 := by
        rw [MvPowerSeries.toAdicCompletion_apply_eq_mk_truncTotal, ht]
        rfl
      rw [AdicCompletion.evalOneₐ, AlgHom.comp_apply,
        ← AdicCompletion.factor_eval_eq_evalₐ P (MvPowerSeries.toAdicCompletion σ R f)
          (by simp only [smul_eq_mul, Ideal.mul_top]; exact le_rfl)]
      simp only [AdicCompletion.eval_apply, hz, map_zero]
    rw [← he] at hm
    obtain ⟨g, hg, hgf⟩ := (Ideal.mem_map_of_equiv e (e f)).mp hm
    exact e.injective hgf ▸ hg
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (MvPowerSeries.constantCoeff_X i)

/-- 局所係数環の有限変数冪級数の極大イデアルは、係数極大イデアルと全変数の和。 -/
theorem powerSeries_maximalIdeal_eq (σ R : Type*) [Finite σ] [CommRing R] [IsLocalRing R] :
    maximalIdeal (MvPowerSeries σ R) =
      (maximalIdeal R).map MvPowerSeries.C ⊔
        Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))) := by
  let f := MvPowerSeries.constantCoeff (σ := σ) (R := R)
  let : IsLocalHom f := ⟨fun _ h ↦ MvPowerSeries.isUnit_iff_constantCoeff.mpr h⟩
  rw [← maximalIdeal_comap f, ← powerSeries_ker_constantCoeff σ R]
  have hmap : ((maximalIdeal R).map (MvPowerSeries.C (σ := σ))).map f =
      maximalIdeal R := by
    rw [Ideal.map_map]
    have he : f.comp MvPowerSeries.C = RingHom.id R := by ext; simp [f]
    rw [he, Ideal.map_id]
  nth_rw 1 [← hmap]
  rw [Ideal.comap_map_of_surjective f (fun r ↦ ⟨MvPowerSeries.C r, by simp [f]⟩)]
  rfl

/-- Witt係数冪級数の極大イデアルは(p)と全変数で生成される。 -/
theorem wittPowerSeries_maximalIdeal_eq (σ k : Type*) [Finite σ] [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k] :
    maximalIdeal (MvPowerSeries σ (WittVector p k)) =
      Ideal.span {(p : MvPowerSeries σ (WittVector p k))} ⊔
        Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := WittVector p k))) := by
  rw [powerSeries_maximalIdeal_eq, (WittVector.irreducible p).maximalIdeal_eq,
    Ideal.map_span]
  simp only [Set.image_singleton, map_natCast]

/-- 完備Noether局所係数環の有限変数冪級数環は極大イデアル進完備。 -/
theorem isAdicComplete_powerSeries_maximalIdeal (σ R : Type*) [Finite σ]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal (MvPowerSeries σ R)) (MvPowerSeries σ R) := by
  rw [powerSeries_maximalIdeal_eq]
  exact isAdicComplete_powerSeries_coefficients_sup_variables σ R (maximalIdeal R)

end SerrePositivity
