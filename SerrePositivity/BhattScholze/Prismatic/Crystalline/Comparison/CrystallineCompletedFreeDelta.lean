module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaResidue
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaBounds
import Mathlib.Algebra.MvPolynomial.Equiv
import all SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaResidue

/-!
# 結晶基底上の完備自由 δ 環の剰余

## 概要
結晶基底上の完備自由 δ 環は p 正則で、p で割ると素数体上の多項式環になる。

## 方針
基底生成元による剰余比較を使い、p が零の係数環上では p 完備化の単位を反転する。

## 規約
剰余の変数は初期変数とその反復 δ 座標。

## 使われ方
Frobenius の完全平坦性と結晶比較。
-/

public noncomputable section

open SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

/-- 指定した主元が零なら、主元完備化の単位は環同型を与える。 -/
def crystallinePrincipalCompletionOfZero {R : Type u} [CommRing R] (a : R) (ha : a = 0) :
    letI := principalCompletionCommRing R a
    PrincipalCompletionH0 R a ≃+* R := by
  let := principalCompletionCommRing R a
  let j := principalCompletionUnitRingHom R a
  have hR : letI := (RingHom.id R).toAlgebra; IsModuleComplete R a (ModuleCat.of R R) := by
    apply isModuleComplete_of_pow_smul_zero R a _ 1
    intro x
    simp [ha]
  let l := principalCompletionLift R a R (RingHom.id R) hR
  have hl : l.comp j = RingHom.id R := principalCompletionLift_comp R a R (RingHom.id R) hR
  have hj : j.comp l = RingHom.id _ := by
    have hH := principalCompletion_isModuleComplete_unit a
    exact (principalCompletion_existsUnique_ringHom R a _ j hH).unique (by
      rw [RingHom.comp_assoc, hl, RingHom.comp_id]) (RingHom.id_comp _)
  exact RingEquiv.ofRingHom l j hl hj

/-- 零元での完備化の同一視は単位を恒等射に送る。 -/
theorem crystallinePrincipalCompletionOfZero_unit {R : Type u} [CommRing R]
    (a : R) (ha : a = 0) (x : R) :
    letI := principalCompletionCommRing R a
    crystallinePrincipalCompletionOfZero a ha (principalCompletionUnitRingHom R a x) = x := by
  let := principalCompletionCommRing R a
  exact (crystallinePrincipalCompletionOfZero a ha).apply_symm_apply x

variable (p : ℕ) [Fact p.Prime] (S : Type u)

local notation "Z" => (crystallineBasePrism p)
local notation "B" => completedFreeDelta Z S

private theorem completedFreeDelta_base_generator :
    completedFreeDeltaBase Z S (Z).generator = (p : B) := by
  rw [crystallineBase_generator, map_natCast]

/-- 結晶基底上の完備自由 δ 環は p で正則。 -/
theorem crystallineCompletedFreeDelta_primeRegular :
    IsSMulRegular B (p : B) := by
  have h := completedFreeDelta_generator_regular Z (crystallineBaseBounded p) S
  rw [completedFreeDelta_base_generator p S] at h
  exact h

/-- 結晶基底上の完備自由 δ 環の mod p は、反復 δ 座標を変数とする多項式環。 -/
def crystallineCompletedFreeDeltaResidue :
    (B ⧸ Ideal.span {(p : B)}) ≃+* MvPolynomial (S × ℕ) (ZMod p) := by
  let R := MvPolynomial (S × ℕ) (cartierBase.{u} p)
  have hp : (p : R) = 0 := by
    rw [← map_natCast (MvPolynomial.C : cartierBase p →+* R), cartierBase_natCast, map_zero]
  let := principalCompletionCommRing R (p : R)
  let e := completedFreeDeltaResidueEquiv Z S
  exact (Ideal.quotEquivOfEq (congrArg (fun x : B => Ideal.span {x})
    (completedFreeDelta_base_generator p S).symm)).trans
      (e.trans ((crystallinePrincipalCompletionOfZero (p : R) hp).trans
        (MvPolynomial.mapEquiv (S × ℕ) (cartierBaseEquiv p))))

local notation "B₀" => RelativeFreeDeltaRing (R := crystallineBase p) S

/-- 結晶基底上の自由 δ 環から完備自由 δ 環への単位。 -/
def crystallineCompletedFreeDeltaUnit : B₀ →+* B :=
  pdCompletionUnit B₀ p (algebraMap (crystallineBase p) B₀ (Z).generator)

/-- 完備化の単位は δ 射。 -/
theorem crystallineCompletedFreeDeltaUnit_isDeltaHom :
    (relativeFreeDeltaStructure S (Z).deltaStructure).IsDeltaHom
      (completedFreeDeltaStructure Z S) (crystallineCompletedFreeDeltaUnit p S) :=
  pdCompletionUnit_isDeltaHom _ _

/-- 結晶基底上の自由 δ 環は p で正則。 -/
theorem crystallineRawFreeDelta_primeRegular : IsSMulRegular B₀ (p : B₀) := by
  intro x y h
  have hp := (Z).generator_regular
  rw [crystallineBase_generator] at hp
  apply MvPolynomial.ext
  intro m
  apply hp
  change (p : B₀) * x = (p : B₀) * y at h
  have h' := congrArg (fun g : B₀ => g.coeff m) h
  rw [← map_natCast (MvPolynomial.C : crystallineBase p →+* B₀),
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul] at h'
  exact h'

private theorem rawC_generator :
    (MvPolynomial.C (Z).generator : B₀) = (p : B₀) := by
  rw [crystallineBase_generator, map_natCast]

/-- 結晶基底上の自由 δ 環の mod p は素数体上の多項式環。 -/
def crystallineRawFreeDeltaResidue :
    (B₀ ⧸ Ideal.span {(p : B₀)}) ≃+* MvPolynomial (S × ℕ) (ZMod p) :=
  (Ideal.quotEquivOfEq (congrArg (fun x : B₀ => Ideal.span {x}) (rawC_generator p S).symm)).trans
    ((polynomialQuotientEquiv (σ := S × ℕ) (Z).generator).trans
      (MvPolynomial.mapEquiv (S × ℕ) (cartierBaseEquiv p)))

/-- 完備化の単位は、反復 δ 座標による二つの剰余表示を結ぶ。 -/
theorem crystallineCompletedFreeDeltaResidue_unit (x : B₀) :
    crystallineCompletedFreeDeltaResidue p S
      (Ideal.Quotient.mk _ (crystallineCompletedFreeDeltaUnit p S x)) =
    crystallineRawFreeDeltaResidue p S (Ideal.Quotient.mk _ x) := by
  let R := MvPolynomial (S × ℕ) (cartierBase.{u} p)
  let := principalCompletionCommRing R (p : R)
  have hp : (p : R) = 0 := by
    rw [← map_natCast (MvPolynomial.C : cartierBase p →+* R), cartierBase_natCast, map_zero]
  let e := MvPolynomial.mapEquiv (S × ℕ) (cartierBaseEquiv p)
  change e (crystallinePrincipalCompletionOfZero (p : R) hp
      (completedFreeDeltaResidueEquiv Z S (Ideal.Quotient.mk _
        (pdCompletionUnit B₀ p (algebraMap (crystallineBase p) B₀ (Z).generator) x)))) =
    e (polynomialQuotientEquiv (σ := S × ℕ) (Z).generator (Ideal.Quotient.mk _ x))
  rw [completedFreeDeltaResidueEquiv_unit, crystallinePrincipalCompletionOfZero_unit]
  rfl

end SerrePositivity.BhattScholze.Prismatic
