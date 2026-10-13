module

public import SerrePositivity.CommutativeAlgebra.PrimaryParameterExistence
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # 指定された非零因子を含むパラメータ系

極大イデアル内の非零因子で商を取り、既存のパラメータ選択を適用して持ち上げる。
整域性・正則性・Cohen–Macaulay性・完備性は一般定理に要求しない。
-/

public section
namespace SerrePositivity
open IsLocalRing

/-- 次元r+1のNoether局所環で、極大イデアル内の非零因子による商の次元はr。 -/
theorem ringKrullDim_quotient_eq_of_nonZeroDivisor
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ nonZeroDivisors R) (hm : x ∈ maximalIdeal R)
    {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ringKrullDim (R ⧸ Ideal.span {x}) = r := by
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hx)
    (ringJacobson_eq_maximalIdeal (R := R) ▸ hm)
  rw [hdim] at h
  exact le_antisymm (ENat.WithBot.add_le_add_one_right_iff.mp h.le)
    (ENat.WithBot.add_le_add_one_right_iff.mp h.ge)

/-- 指定非零因子にr個の元を加えて極大イデアル準素のイデアルを作る。
商で選んだパラメータを持ち上げ、根基の等式を商写像に沿って戻す。 -/
theorem exists_parameters_completing_nonZeroDivisor
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ nonZeroDivisors R) (hm : x ∈ maximalIdeal R)
    {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ∃ y : Fin r → R, (∀ i, y i ∈ maximalIdeal R) ∧
      (Ideal.span {x} ⊔ Ideal.span (Set.range y)).radical = maximalIdeal R := by
  classical
  let I : Ideal R := Ideal.span {x}
  have hI : I ≤ maximalIdeal R := by rwa [Ideal.span_singleton_le_iff_mem]
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  let : IsNoetherianRing (R ⧸ I) :=
    isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mk I
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hd : ringKrullDim (R ⧸ I) = r :=
    ringKrullDim_quotient_eq_of_nonZeroDivisor R x hx hm hdim
  have ht := PrimaryParameterExistence.exists_parameters_in_primary
    (R ⧸ I) (maximalIdeal (R ⧸ I)) (Ideal.IsPrime.radical inferInstance)
  have hn : dimToNat (ringKrullDim (R ⧸ I)) = r := by simp [hd, dimToNat]
  rw [hn] at ht
  obtain ⟨z, hz, hrad⟩ := ht
  choose y hy using (fun i : Fin r ↦ Ideal.Quotient.mk_surjective (z i))
  have hym (i : Fin r) : y i ∈ maximalIdeal R := by
    rw [← maximalIdeal_comap q]
    change q (y i) ∈ maximalIdeal (R ⧸ I)
    rw [hy]
    exact hz i
  let J := I ⊔ Ideal.span (Set.range y)
  have hmap : J.map q = Ideal.span (Set.range z) := by
    change (I ⊔ Ideal.span (Set.range y)).map (Ideal.Quotient.mk I) = _
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span,
      ← Set.range_comp]
    rw [show (Ideal.Quotient.mk I) ∘ y = z from funext hy]
  have hcomap : (J.map q).comap q = J := by
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective]
    change J ⊔ RingHom.ker q = J
    rw [show RingHom.ker q = I from Ideal.mk_ker]
    exact sup_eq_left.mpr le_sup_left
  refine ⟨y, hym, ?_⟩
  change J.radical = maximalIdeal R
  calc
    J.radical = ((J.map q).radical).comap q := by rw [Ideal.comap_radical, hcomap]
    _ = (maximalIdeal (R ⧸ I)).comap q := by rw [hmap, hrad]
    _ = maximalIdeal R := maximalIdeal_comap q

/-- 次元1の場合、極大イデアル内の非零因子の主イデアル自体が極大イデアル準素。
残りのパラメータが空列である境界を明示する。 -/
theorem radical_span_eq_maximalIdeal_of_nonZeroDivisor_of_dim_one
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ nonZeroDivisors R) (hm : x ∈ maximalIdeal R)
    (hdim : ringKrullDim R = 1) : (Ideal.span {x}).radical = maximalIdeal R := by
  obtain ⟨y, _, hrad⟩ := exists_parameters_completing_nonZeroDivisor R x hx hm
    (r := 0) (by simpa using hdim)
  simpa using hrad

/-- 指定非零因子を先頭に置いたパラメータ系。 -/
theorem exists_systemOfParameters_with_first_nonZeroDivisor
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ nonZeroDivisors R) (hm : x ∈ maximalIdeal R)
    {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ∃ z : Fin (r + 1) → R, z 0 = x ∧ (∀ i, z i ∈ maximalIdeal R) ∧
      IsSystemOfParameters R z := by
  obtain ⟨y, hy, hrad⟩ := exists_parameters_completing_nonZeroDivisor R x hx hm hdim
  refine ⟨Fin.cons x y, Fin.cons_zero _ _, ?_, hdim, ?_⟩
  · intro i
    exact Fin.cases hm hy i
  · rw [Fin.range_cons, Ideal.span_insert]
    exact hrad

end SerrePositivity
