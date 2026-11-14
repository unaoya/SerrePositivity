module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDDeltaFrobeniusEvaluation
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialFunctor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDDeltaFrobeniusEvaluation
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialFunctor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 結晶の δ 除算模型から小さい分冪模型への射

## 概要
ℤ_p 上の Frobenius 差の δ 除算模型を、通常の完備分冪模型へ写す。

## 方針
小さい分冪包の変数の δ を零にして評価し、既存の小さい模型の比較同型を通す。

## 規約
自由 δ 環の初期座標の像を明記する。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の結晶の橋を小さい分冪模型に移す。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetraction

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "k" => crystallineBase p
local notation "Z" => crystallineBasePrism p
local notation "Jp" => Ideal.span {(p : k)}

private theorem local_base (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : crystallineBase.{u} p) := by
  have h : IsUnit (m : PadicInt p) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hm))
  simpa only [map_natCast] using h.map (ULift.ringEquiv : crystallineBase.{u} p ≃+* PadicInt p).symm

local notation "γ" => residuePdStructure p (crystallineBase_regular p) (local_base p)
private theorem base_prime : (p : k) ∈ Jp := Ideal.subset_span rfl

private def polynomial : Poly k := ⟨r⟩

local notation "hp" => base_prime p
local notation "Q" => polynomial p r
local notation "hk" => crystallineBase_complete p
local notation "hr" => crystallineBase_regular p
local notation "hkern" => PDPolynomialFunctor.base_ker (J := Jp) Q
local notation "frame" => PDPolynomialFunctor.frame (J := Jp) Q
local notation "E" n => PDCechNerve.term p γ hp hkern frame n

private abbrev envelope (n : ℕ) :=
  PDCechNerve.term.{u} p γ hp hkern frame n

private theorem frobenius_base : (Jp).map (Z).deltaStructure.frobeniusLift ≤ Jp := by
  change (Jp).map (crystallineBaseDelta p).frobeniusLift ≤ Jp
  rw [crystallineBaseDelta_frobenius, Ideal.map_id]

private def termEquiv (n : ℕ) : pdTerm p k r n ≃ₐ[k] (E n).carrier :=
  PDSmallModelComparison.termEquiv p k γ hp hk hr r hkern n

private theorem regular (n : ℕ) :
    Function.Injective (fun x : (E n).carrier => (p : (E n).carrier) * x) := by
  let e := termEquiv p r n
  intro x y h
  apply e.symm.injective
  have h' := congrArg (fun x : (E n).carrier => e.symm x) h
  simp only [map_mul, map_natCast] at h'
  apply principalCompletionH0_smul_injective_of_regular (pdRaw k r n) (p : pdRaw k r n)
    (PDSmallRawEnvelope.raw_regular p r n hr)
  have h'' : p • (e.symm x : pdTerm p k r n) = p • (e.symm y : pdTerm p k r n) := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    exact h'
  simpa only [Nat.cast_smul_eq_nsmul] using h''

private theorem difference_mem (n : ℕ) (j : Fin r) (i : Fin (n + 1)) :
    (E n).unit (MvPolynomial.X (ULift.up j, i)) -
      (E n).unit (MvPolynomial.X (ULift.up j, 0)) ∈ (E n).ideal := by
  rw [← PDCechNerve.augmentation_ker]
  apply RingHom.mem_ker.mpr
  rw [map_sub]
  change PDCechNerve.augmentation p γ hp hkern frame n
      (PDCechNerve.variableImage p γ hp hkern frame n (ULift.up j, i)) -
    PDCechNerve.augmentation p γ hp hkern frame n
      (PDCechNerve.variableImage p γ hp hkern frame n (ULift.up j, 0)) = 0
  rw [PDCechNerve.augmentation_variableImage, PDCechNerve.augmentation_variableImage, sub_self]

private def evaluate (n : ℕ) : (pdDeltaRings.{u} p r).obj ⦋n⦌ →+* (E n).carrier := by
  exact pdFrobeniusDivisionEvaluation Z r n γ (E n) (regular p r n) (local_base p)
    (frobenius_base p) (crystallineBase_generator p) (difference_mem p r n)

private def envelopeMap {m n : SimplexCategory} (θ : m ⟶ n) :
    (envelope.{u} p r m.len).carrier →ₐ[crystallineBase.{u} p]
      (envelope.{u} p r n.len).carrier :=
  PDCechNerve.mapCopies p γ hp hkern frame θ.toOrderHom

private theorem envelopeMap_dp {m n : SimplexCategory} (θ : m ⟶ n) :
    (envelope.{u} p r m.len).dividedPowers.IsDPMorphism
      (envelope.{u} p r n.len).dividedPowers (envelopeMap.{u} p r θ).toRingHom :=
  PDCechNerve.mapCopies_isDPMorphism p γ hp hkern frame θ.toOrderHom

private theorem envelopeMap_variable {m n : SimplexCategory} (θ : m ⟶ n)
    (j : ULift.{u} (Fin r)) (i : Fin (m.len + 1)) :
    envelopeMap.{u} p r θ ((envelope.{u} p r m.len).unit (MvPolynomial.X (j, i))) =
      (envelope.{u} p r n.len).unit (MvPolynomial.X (j, θ.toOrderHom i)) :=
  PDCechNerve.mapCopies_variableImage p γ hp hkern frame θ.toOrderHom (j, i)

private theorem envelopeMap_termEquiv {m n : SimplexCategory} (θ : m ⟶ n)
    (x : pdTerm p (crystallineBase.{u} p) r m.len) :
    termEquiv.{u} p r n.len (((pdModel p (crystallineBase.{u} p) r).map θ).right.hom x) =
      envelopeMap.{u} p r θ (termEquiv.{u} p r m.len x) := by
  have he := PDSmallModelComparison.termIso_natural p (crystallineBase.{u} p) γ hp hk hr r hkern θ
  exact ConcreteCategory.congr_hom (congrArg Under.Hom.right he) x

/-- 初期座標を通常の小さい分冪模型へ送る結晶の環射。 -/
def retractAt (n : ℕ) : (pdDeltaRings.{u} p r).obj ⦋n⦌ →+* pdTerm p k r n :=
  (termEquiv p r n).symm.toRingHom.comp (evaluate p r n)

private theorem evaluate_variable (n : ℕ) (j : Fin r) (i : Fin (n + 1)) :
    evaluate p r n (pdDeltaUnit p r ⦋n⦌ (affineVariable Z r n j i)) =
      (E n).unit (MvPolynomial.X (ULift.up j, i)) := by
  unfold evaluate pdDeltaUnit crystallinePDDifference
  have h := pdFrobeniusDivisionEvaluation_variable Z r n γ (E n) (regular p r n)
    (local_base p) (frobenius_base p) (crystallineBase_generator p) (difference_mem p r n) j i
  unfold pdFrobeniusDifference at h
  exact h

private theorem at_variable (n : ℕ) (j : Fin r) (i : Fin (n + 1)) :
    retractAt p r n (pdDeltaUnit p r ⦋n⦌ (affineVariable Z r n j i)) =
      principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n))
        (PDSmallRawEnvelope.unit r n (MvPolynomial.X (ULift.up j, i))) := by
  apply (termEquiv p r n).injective
  change termEquiv p r n ((termEquiv p r n).symm
    (evaluate p r n (pdDeltaUnit p r ⦋n⦌ (affineVariable Z r n j i)))) = _
  rw [AlgEquiv.apply_symm_apply]
  rw [evaluate_variable]
  exact ((PDSmallModelComparison.termEquiv_unit p k γ hp hk hr r hkern n _).trans
    (PDSmallModelComparison.rawToFrame_unit p k γ hp hk hr r hkern n _)).symm

end SerrePositivity.BhattScholze.Prismatic.CrystallinePDRetraction
