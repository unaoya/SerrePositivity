module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Over

/-!
# 正則局所環・局所環の標準事実（層 3a）

Mathlib にない標準事実を `sorry` つきの定理として置く。`notes/PLAN.md` §11 の A1 など。

- 正則局所環の正則パラメータ系は（弱）正則列。
- 局所環 `A` 上有限な局所環 `T` では、`m_T` の冪が `m_A T` に入る（`T/m_A T` は Artin 局所環）。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- **A1**：正則局所環の正則パラメータ系は弱正則列（層 3a、未証明）。 -/
theorem isWeaklyRegular_of_span_eq_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {e : ℕ} (z : Fin e → A) (_hz : Ideal.span (Set.range z) = maximalIdeal A)
    (_he : ringKrullDim A = e) : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z) := by
  sorry

/-- 局所環 `A` 上有限な局所環 `T` では `m_T^N ≤ m_A T` となる `N` がある（層 3a、証明済み）。 -/
theorem exists_pow_maximalIdeal_le_map (A T : Type u) [CommRing A] [IsLocalRing A] [CommRing T]
    [IsLocalRing T] [Algebra A T] (hfin : Module.Finite A T) :
    ∃ N : ℕ, (maximalIdeal T) ^ N ≤ (maximalIdeal A).map (algebraMap A T) := by
  set I := (maximalIdeal A).map (algebraMap A T)
  let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  have hf : Module.Finite (A ⧸ maximalIdeal A) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have : IsArtinianRing (T ⧸ I) := IsArtinianRing.of_finite (A ⧸ maximalIdeal A) (T ⧸ I)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T ⧸ I)
  refine ⟨n, ?_⟩
  have hle : (maximalIdeal T).map (Ideal.Quotient.mk I) ≤ (⊥ : Ideal (T ⧸ I)).jacobson := by
    rw [Ideal.jacobson, le_sInf_iff]
    rintro J ⟨-, hJ⟩
    rw [Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _
      Ideal.Quotient.mk_surjective (K := J))).ge
  have : ((maximalIdeal T) ^ n).map (Ideal.Quotient.mk I) = ⊥ := by
    rw [Ideal.map_pow]
    exact le_bot_iff.mp ((Ideal.pow_right_mono hle n).trans (by rw [hn]; rfl))
  rwa [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at this

end SerrePositivity
