module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# 局所環上の有限代数

- 商環 `R ⧸ I` 上の加群は `I` で消える。商加群の零化イデアルは元の零化イデアルを含む。
- 剰余体への射 `R → T → T/m_T` が全射なら、剰余体の同型 `ResidueField R ≃+* ResidueField T` がある。
- 局所環 `R` 上有限な局所環 `T` では、`m_T` のある冪が `m_R T` に入る（`T / m_R T` は Artin 環）。
  正規化長さの定義域のイデアルを `m_R C` と `m_T C` の間で取り替えるのに使う
  （`Paper/Lemma3_4.lean`、`Inputs/LengthAlgebra.lean`、`Core/NormApplication.lean`）。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 商環 `R ⧸ I` 上の加群は `I` で消える。 -/
lemma quotient_action_annihilator (I : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] :
    I ≤ Module.annihilator R M := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  rw [← IsScalarTower.algebraMap_smul (R ⧸ I) r x]
  have hz : algebraMap R (R ⧸ I) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [hz, zero_smul]

/-- 商加群の零化イデアルは元の零化イデアルを含む。 -/
lemma annihilator_le_quotient (M : Type u) [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Module.annihilator R M ≤ Module.annihilator R (M ⧸ N) := by
  intro r hr
  rw [Module.mem_annihilator] at hr ⊢
  intro x
  obtain ⟨x, rfl⟩ := N.mkQ_surjective x
  rw [← N.mkQ.map_smul, hr, map_zero]

/-- 剰余体への射が全射なら、剰余体は同型。 -/
noncomputable def residueFieldEquiv_of_surjective [IsLocalRing R]
    (T : Type u) [CommRing T] [IsLocalRing T] [Algebra R T]
    (hres : Function.Surjective ((residue T).comp (algebraMap R T))) :
    ResidueField R ≃+* ResidueField T := by
  let f := (residue T).comp (algebraMap R T)
  have : (RingHom.ker f).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective f hres (K := ⊥)
  have hk : RingHom.ker f = maximalIdeal R := IsLocalRing.eq_maximalIdeal inferInstance
  exact (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hres)

/-- 局所環 `R` 上有限な局所環 `T` では、`m_T` のある冪が `m_R T` に入る。 -/
theorem maximalIdeal_pow_le_map_of_finite [IsLocalRing R]
    (T : Type u) [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T] :
    ∃ n : ℕ, (maximalIdeal T) ^ n ≤ (maximalIdeal R).map (algebraMap R T) := by
  let I := (maximalIdeal R).map (algebraMap R T)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  have : Module.Finite R (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite (R ⧸ maximalIdeal R) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (T ⧸ I) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  exact IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I

end SerrePositivity
