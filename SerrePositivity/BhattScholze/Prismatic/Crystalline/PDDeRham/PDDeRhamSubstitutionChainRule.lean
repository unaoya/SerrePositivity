module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamSubstitutionJacobian
import Mathlib.Algebra.TrivSqZeroExt.Basic
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawPolynomialSubstitution
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamSubstitutionJacobian
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDFrobeniusLift
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawDifferential

/-!
## 概要
多項式代入に対する未完備の分冪偏微分の連鎖律を示す。

## 方針
二つの導分を平方零拡大への射として比較し、自由分冪の生成元で階乗を掛け、標的で消去する。

## 規約
素数p、分冪構造、p進完備性とp乗法の単射性の仮定を明示し、未完備係数環で証明する。

## 使われ方
分冪de Rham複体で、多項式代入と微分の両立を検査する。
-/

public noncomputable section

open CategoryTheory Algebra.TensorProduct
open scoped Simplicial BigOperators TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime]
variable {J : Ideal k} (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hr : Function.Injective (fun x : k => (p : k) * x))
variable {Q Q' : Poly k} (f : Q ⟶ Q') (n : ℕ)

local notation "RawS" => pdRaw k Q.n n
local notation "RawT" => pdRaw k Q'.n n
local notation "F" => substitute p γ hk hr f n

include hk hr in
private theorem factorial_regular (q : ℕ) :
    Function.Injective (fun x : RawT => (q.factorial : RawT) * x) := by
  have hlocal (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : RawT) := by
    simpa only [map_natCast] using
      (PDSmallRawEnvelope.isUnit_natCast_of_not_dvd p hk m hm).map (algebraMap k RawT)
  have hreg : Function.Injective (fun z : RawT => (p : RawT) * z) := by
    intro a b hab
    exact PDSmallRawEnvelope.raw_regular p Q'.n n hr hab
  exact SerrePositivity.BhattScholze.Prismatic.factorial_regular (p := p) (R := RawT)
    hreg hlocal q

private theorem jet_ext (d e : RawS →ₗ[k] RawT)
    (hd : ∀ x y, d (x * y) = F x * d y + F y * d x)
    (he : ∀ x y, e (x * y) = F x * e y + F y * e x)
    (hX : ∀ j, d (baseVar k Q.n ⦋n⦌ j) = e (baseVar k Q.n ⦋n⦌ j))
    (hDP : ∀ x, d (dpCoordinate k Q.n (n := ⦋n⦌) 1 x) =
      e (dpCoordinate k Q.n (n := ⦋n⦌) 1 x)) : d = e := by
  let a : RawS →ₐ[k] RawT := F
  let L : RawS →ₐ[k] TrivSqZeroExt RawT RawT :=
    relativeDerivationJet k (A := RawS) (B := RawT) a d hd
  let R : RawS →ₐ[k] TrivSqZeroExt RawT RawT :=
    relativeDerivationJet k (A := RawS) (B := RawT) a e he
  have H : L = R := by
    apply Algebra.TensorProduct.ext
    · apply MvPolynomial.algHom_ext
      intro j
      exact TrivSqZeroExt.ext rfl (hX j)
    · let inc : DividedPowerAlgebra k ((Fin Q.n × Fin n) →₀ k) →ₐ[k] RawS := includeRight
      change L.comp inc = R.comp inc
      refine @DividedPowerAlgebra.algHom_ext k ((Fin Q.n × Fin n) →₀ k)
        _ _ _ (TrivSqZeroExt RawT RawT) _ _ (L.comp inc) (R.comp inc) ?_
      intro q x
      refine TrivSqZeroExt.ext (by rfl) ?_
      change (L (dpCoordinate k Q.n (n := ⦋n⦌) q x)).snd =
        (R (dpCoordinate k Q.n (n := ⦋n⦌) q x)).snd
      have hq : (q.factorial : RawS) * dpCoordinate k Q.n (n := ⦋n⦌) q x =
          (dpCoordinate k Q.n (n := ⦋n⦌) 1 x) ^ q := by
        simpa only [map_mul, map_natCast, map_pow] using
          congrArg (includeRight : DividedPowerAlgebra k ((Fin Q.n × Fin n) →₀ k) →ₐ[k] RawS)
            (DividedPowerAlgebra.natFactorial_mul_dp_eq q x)
      have h₁ : L (dpCoordinate k Q.n (n := ⦋n⦌) 1 x) =
          R (dpCoordinate k Q.n (n := ⦋n⦌) 1 x) := TrivSqZeroExt.ext rfl (hDP x)
      have hL := congrArg (fun z : RawS => L z) hq
      have hR := congrArg (fun z : RawS => R z) hq
      simp only [map_mul, map_natCast, map_pow] at hL hR
      have h := hL.trans ((congrArg (fun z => z ^ q) h₁).trans hR.symm)
      apply factorial_regular (Q' := Q') p hk hr n q
      simpa only [map_mul, map_pow, map_natCast, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.snd_natCast, TrivSqZeroExt.fst_natCast, smul_zero, add_zero, smul_eq_mul]
        using congrArg (fun z : TrivSqZeroExt RawT RawT => z.snd) h
  exact LinearMap.ext fun x =>
    congrArg (fun a : RawS →ₐ[k] TrivSqZeroExt RawT RawT => (a x).snd) H

private def partialBefore (b : pdCoordinates Q'.n n) : RawS →ₗ[k] RawT :=
  (pdRawPartial k Q'.n n b).comp (F).toLinearMap

private def partialAfter (b : pdCoordinates Q'.n n) : RawS →ₗ[k] RawT :=
  ∑ a : pdCoordinates Q.n n,
    jacobian f n b a • ((F).toLinearMap.comp (pdRawPartial k Q.n n a))

private theorem partialBefore_leibniz (b : pdCoordinates Q'.n n) (x y : RawS) :
    partialBefore p γ hk hr f n b (x * y) =
      F x * partialBefore p γ hk hr f n b y + F y * partialBefore p γ hk hr f n b x := by
  change pdRawPartial k Q'.n n b (F (x * y)) = _
  rw [map_mul]
  change pdRawPartial k Q'.n n b (F x * F y) =
    F x * pdRawPartial k Q'.n n b (F y) + F y * pdRawPartial k Q'.n n b (F x)
  rw [← pdRawDerivation_toLinearMap]
  exact (pdRawDerivation k Q'.n n b).leibniz' _ _

private theorem partialAfter_leibniz (b : pdCoordinates Q'.n n) (x y : RawS) :
    partialAfter p γ hk hr f n b (x * y) =
      F x * partialAfter p γ hk hr f n b y + F y * partialAfter p γ hk hr f n b x := by
  simp only [partialAfter, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, ← pdRawDerivation_toLinearMap, Derivation.coeFn_coe,
    Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem partial_copy (b : pdCoordinates Q'.n n) (j : Fin Q.n) (i : Fin (n + 1)) :
    partialBefore p γ hk hr f n b (copy k Q.n ⦋n⦌ j i) =
      partialAfter p γ hk hr f n b (copy k Q.n ⦋n⦌ j i) := by
  classical
  simp only [partialBefore, partialAfter, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, smul_eq_mul, substitute_copy]
  have hp (a : pdCoordinates Q.n n) := copy_partial k Q.n ⦋n⦌ j i a
  simp_rw [hp, AlgHom.commutes]
  change vertexPartial f n i b (MvPolynomial.X j) = _
  refine Fin.cases ?_ (fun i => ?_) i
  · simp_rw [copyToCoordinate_zero k Q.n ⦋n⦌ j]
    simp [Finsupp.single_apply, jacobian, mul_ite, eq_comm]
  · simp_rw [copyToCoordinate_succ k Q.n ⦋n⦌ j i]
    have hs (a c : pdCoordinates Q.n n) :
        jacobian f n b a * algebraMap k RawT (Finsupp.single c (1 : k) a) =
          if a = c then jacobian f n b a else 0 := by
      by_cases h : a = c
      · subst c
        simp only [Finsupp.single_eq_same, map_one, mul_one, ite_true]
      · simp only [Finsupp.single_eq_of_ne h, map_zero, mul_zero, ite_eq_right h]
    simp only [Finsupp.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    simp_rw [hs]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, jacobian]
    abel

private theorem partials_eq (b : pdCoordinates Q'.n n) :
    partialBefore p γ hk hr f n b = partialAfter p γ hk hr f n b := by
  let L := partialBefore p γ hk hr f n b
  let R := partialAfter p γ hk hr f n b
  apply jet_ext p γ hk hr f n L R
    (partialBefore_leibniz p γ hk hr f n b) (partialAfter_leibniz p γ hk hr f n b)
  · intro j
    simpa [copy, vertexDiff, DividedPowerAlgebra.dp_null_of_ne_zero] using
      partial_copy p γ hk hr f n b j 0
  · let ι : ((Fin Q.n × Fin n) →₀ k) →ₗ[k] RawS :=
      (includeRight : DividedPowerAlgebra k ((Fin Q.n × Fin n) →₀ k) →ₐ[k] RawS).toLinearMap.comp
        (DividedPowerAlgebra.embed k _)
    have hι : L.comp ι = R.comp ι := by
      apply (Finsupp.basisSingleOne (R := k)).ext
      rintro ⟨j, i⟩
      change L (dpCoordinate k Q.n (n := ⦋n⦌) 1 (Finsupp.single (j, i) 1)) =
        R (dpCoordinate k Q.n (n := ⦋n⦌) 1 (Finsupp.single (j, i) 1))
      have h := partial_copy p γ hk hr f n b j i.succ
      change L (copy k Q.n ⦋n⦌ j i.succ) = R (copy k Q.n ⦋n⦌ j i.succ) at h
      have h₀ := partial_copy p γ hk hr f n b j 0
      change L (copy k Q.n ⦋n⦌ j 0) = R (copy k Q.n ⦋n⦌ j 0) at h₀
      simp only [copy, vertexDiff, Fin.cases_zero, map_zero, add_zero] at h₀
      simp only [copy, vertexDiff, Fin.cases_succ, map_add, h₀] at h
      exact add_left_cancel h
    intro x
    exact DFunLike.congr_fun hι x

/-- 未完備分冪模型の多項式代入と偏微分の連鎖律。 -/
theorem substitute_partial (b : pdCoordinates Q'.n n) (x : RawS) :
    pdRawPartial k Q'.n n b (F x) =
      ∑ a : pdCoordinates Q.n n, jacobian f n b a * F (pdRawPartial k Q.n n a x) := by
  have h := DFunLike.congr_fun (partials_eq p γ hk hr f n b) x
  simpa only [partialBefore, partialAfter, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, smul_eq_mul] using h

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
