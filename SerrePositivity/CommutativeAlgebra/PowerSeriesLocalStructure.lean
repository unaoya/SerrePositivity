module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesMixedCompleteness
public import SerrePositivity.CommutativeAlgebra.PowerSeriesAdicTopology

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
  ext f
  simpa [RingHom.mem_ker, Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] using
    (mem_powerSeries_variables_pow_iff 1 f).symm

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
