module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequence.RegularSequencePDKoszul
public import SerrePositivity.CommutativeAlgebra.KoszulRegular.PrincipalReduction

/-!
# 正則列に沿う分冪表示の p 正則性

## 概要
p 正則な係数環で、剰余上 Koszul 正則な列に沿う分冪表示は p 正則（BS 著者版 Lemma 2.38）。

## 方針
自由分冪代数を剰余に移し、表示関係の Koszul 分解の H⁰ に p 正則性を移す。

## 規約
一般の有限 Koszul 正則列を扱う。

## 使われ方
階乗部分環との同定と分冪包の普遍性。
-/

public noncomputable section

open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {r : ℕ}

local notation "G" => DividedPowerAlgebra A (Fin r →₀ A)
local notation "I" => Ideal.span {(p : A)}
local notation "B" => A ⧸ I
local notation "G₀" => DividedPowerAlgebra B (Fin r →₀ B)
local notation "I₀" => Ideal.span {(p : G)}
local notation "f₀" => Ideal.Quotient.mk I

private theorem freeDP_coefficientIdeal_map :
    (I).map (algebraMap A G) = (I₀) := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

private def freeDPModPrimeEquiv : (G ⧸ I₀) ≃+* G₀ :=
  (Ideal.quotEquivOfEq (freeDP_coefficientIdeal_map (p := p) (A := A) (r := r)).symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor G I).toRingEquiv.trans
      (freeDPBaseChangeEquiv (Fin r) A B).toRingEquiv)

private theorem freeDPModPrimeEquiv_dp (i : Fin r) (n : ℕ) :
    (freeDPModPrimeEquiv (p := p) (A := A) (r := r))
      (Ideal.Quotient.mk I₀ (DividedPowerAlgebra.dp A n (Finsupp.single i 1))) =
    DividedPowerAlgebra.dp B n (Finsupp.single i 1) := by
  unfold freeDPModPrimeEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingEquiv.trans_apply]
  change freeDPBaseChangeEquiv (Fin r) A B
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor G I
      (Ideal.Quotient.mk _ (DividedPowerAlgebra.dp A n (Finsupp.single i 1)))) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, freeDPBaseChangeEquiv_dp]

private theorem freeDPModPrimeEquiv_coeff (a : A) :
    (freeDPModPrimeEquiv (p := p) (A := A) (r := r))
      (Ideal.Quotient.mk I₀ (algebraMap A G a)) = algebraMap B G₀ (f₀ a) := by
  unfold freeDPModPrimeEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingEquiv.trans_apply]
  change freeDPBaseChangeEquiv (Fin r) A B
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor G I
      (algebraMap B _ (f₀ a))) = _
  rw [AlgEquiv.commutes, AlgEquiv.commutes]

/-- 概要：分冪の一次関係に p を加えると Koszul 正則。
方針：自由分冪代数の p 正則性と剰余上の関係列の Koszul 計算を合わせる。
規約：BS 著者版 Lemma 2.38 の有限列の場合。
使われ方：表示環の p 正則性と高次 Tor の消滅。 -/
theorem dpFamilyRelations_snoc_isKoszulResolution (a : Fin r → A)
    (hp : IsSMulRegular A (p : A)) (ha : IsKoszulResolution (f₀ ∘ a)) :
    IsKoszulResolution (Fin.snoc (fun i =>
      DividedPowerAlgebra.dp A 1 (Finsupp.single i 1 : Fin r →₀ A) - algebraMap A G (a i)) (p : G)) := by
  let x (i : Fin r) : G :=
    DividedPowerAlgebra.dp A 1 (Finsupp.single i 1) - algebraMap A G (a i)
  have hpG : IsSMulRegular G (p : G) := by
    have h := freeDP_isSMulRegular (Fin r) (p : A) hp
    change Function.Injective (fun y : G => (p : G) * y)
    simpa only [IsSMulRegular, Algebra.smul_def, map_natCast] using h
  have hpB : (p : B) = 0 := by
    rw [← map_natCast f₀]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let e : (G ⧸ I₀) ≃+* G₀ := freeDPModPrimeEquiv
  have hx : IsKoszulResolution (e.toRingHom ∘ Ideal.Quotient.mk I₀ ∘ x) := by
    have he : e.toRingHom ∘ Ideal.Quotient.mk I₀ ∘ x = fun i =>
        DividedPowerAlgebra.dp B 1 (Finsupp.single i 1) - algebraMap B G₀ (f₀ (a i)) := by
      funext i
      change e (Ideal.Quotient.mk I₀
        (DividedPowerAlgebra.dp A 1 (Finsupp.single i 1) - algebraMap A G (a i))) = _
      rw [map_sub, map_sub]
      exact congrArg₂ (· - ·) (freeDPModPrimeEquiv_dp (p := p) (A := A) i 1)
        (freeDPModPrimeEquiv_coeff (p := p) (r := r) (a i))
    rw [he]
    exact dpFamilyRelations_isKoszulResolution_of_prime_zero (f₀ ∘ a) hpB ha
  exact isKoszulResolution_snoc_of_regular_mod (R := G) (S := G₀) x (p : G) hpG e hx

/-- 概要：剰余上で Koszul 正則な列の分冪表示環は p 正則。
方針：関係列に p を加えた Koszul 複体の負一次ホモロジーが消えることを使う。
規約：BS 著者版 Lemma 2.38 の有限列の場合。
使われ方：階乗部分環との同定と分冪包の普遍性。 -/
theorem dpFamilyPresentation_primeRegular (a : Fin r → A)
    (hp : IsSMulRegular A (p : A)) (ha : IsKoszulResolution (f₀ ∘ a)) :
    IsSMulRegular (DPFamilyPresentation a) (p : DPFamilyPresentation a) := by
  have h := isSMulRegular_quotient_of_snoc _ (p : G)
    (dpFamilyRelations_snoc_isKoszulResolution a hp ha)
  change Function.Injective (fun y : DPFamilyPresentation a => (p : DPFamilyPresentation a) * y)
  change Function.Injective (fun y : DPFamilyPresentation a =>
    Ideal.Quotient.mk (dpFamilyRelationIdeal a) (p : G) * y) at h
  simpa only [map_natCast] using h

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.38"] _root_.SerrePositivity.BhattScholze.dpFamilyPresentation_primeRegular
