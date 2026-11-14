module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDEnvelopeCrystallineCoefficientMaps
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawCoefficientPD
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelBaseChange
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawCoefficientPD
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDAdicCompletion
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 小さい分冪枠の係数変更

## 概要
既存の小さい分冪模型の係数変更を、一般の分冪基底上の完備分冪枠の射として読む。

## 方針
主完備化と通常の p 進完備化の比較を通す。
未完備の係数変更の分冪両立を、分離な標的への一意延長で完備枠へ移す。

## 規約
係数環は両側で p 正則かつ p 進完備。基底の分冪との両立を明記する。

## 使われ方
BS 著者版 Theorem 6.4 の結晶の橋の係数変更と、Witt の二比較の照合。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDSmallCoefficientComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k l : Type u) [CommRing k] [CommRing l] [Algebra k l]
variable {J : Ideal k} {I : Ideal l} (γ : DividedPowers J) (ε : DividedPowers I)
variable (hpK : (p : k) ∈ J) (hpL : (p : l) ∈ I)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hl : IsAdicComplete (Ideal.span {(p : l)}) l)
variable (hrK : Function.Injective (fun x : k => (p : k) * x))
variable (hrL : Function.Injective (fun x : l => (p : l) * x)) (r n : ℕ)
variable (hJ : J ≤ RingHom.ker (algebraMap k (MvPolynomial (Fin r) (k ⧸ J))))
variable (hI : I ≤ RingHom.ker (algebraMap l (MvPolynomial (Fin r) (l ⧸ I))))

local notation "sK" => (fun j : ULift (Fin r) =>
  (MvPolynomial.X (ULift.down j) : MvPolynomial (Fin r) (k ⧸ J)))
local notation "sL" => (fun j : ULift (Fin r) =>
  (MvPolynomial.X (ULift.down j) : MvPolynomial (Fin r) (l ⧸ I)))
local notation "D" => PDCechNerve.term p γ hpK hJ sK n
local notation "E" => PDCechNerve.term p ε hpL hI sL n
local notation "RS" => pdRaw k r n
local notation "RT" => pdRaw l r n
local instance : CommRing (PrincipalCompletionH0 RS (p : RS)) :=
  principalCompletionCommRing RS (p : RS)

local notation "cS" => PDSmallModelComparison.principalAdicRingEquiv RS (p : RS)
  (PDSmallRawEnvelope.raw_regular p r n hrK)
local notation "dS" => PDSmallModelComparison.adicEquiv p k γ hpK hk hrK r hJ n
local notation "eS" => PDSmallModelComparison.termEquiv p k γ hpK hk hrK r hJ n
local notation "eT" => PDSmallModelComparison.termEquiv p l ε hpL hl hrL r hI n
local notation "coeff" => CommRingCat.Hom.hom (Under.Hom.right (NatTrans.app (pdModelBaseChange p k l r) ⦋n⦌))

/-- 小さい完備分冪模型の係数変更を、分冪枠の台環の間に移す。 -/
def coefficientMap : (D).carrier →+* (E).carrier :=
  ((eT).toRingHom.comp ((coeff).comp (cS).symm.toRingHom)).comp (dS).symm.toRingHom

local notation "g" => coefficientMap p k l γ ε hpK hpL hk hl hrK hrL r n hJ hI

/-- 枠の係数変更は、既存の完備模型の係数変更を二つの比較同型で挟んだ射。 -/
private theorem coefficientMap_eq_model :
    (g) = (eT).toRingHom.comp ((coeff).comp (eS).symm.toRingHom) := by
  apply RingHom.ext
  intro x
  rfl

omit [Fact p.Prime] in
private theorem inverse_completion_unit (x : RS) :
    (cS).symm ((PDSmallModelComparison.toAdicCompletion p k RS).toRingHom x) =
      principalCompletionUnitRingHom RS (p : RS) x := by
  have h := congrArg (cS).symm
    (PDSmallModelComparison.principalAdicRingEquiv_unit RS (p : RS)
      (PDSmallRawEnvelope.raw_regular p r n hrK) x)
  simp only [RingEquiv.symm_apply_apply] at h
  convert h.symm using 1
  congr 1


/-- 係数変更は分冪枠の各頂点変数を同じ頂点変数に送る。 -/
theorem coefficientMap_variable (j : ULift.{u} (Fin r)) (i : Fin (n + 1)) :
    (g) ((D).unit (MvPolynomial.X (j, i))) = (E).unit (MvPolynomial.X (j, i)) := by
  have hs := PDSmallModelComparison.termEquiv_unit p k γ hpK hk hrK r hJ n
    (PDSmallRawEnvelope.unit r n (MvPolynomial.X (j, i)))
  rw [PDSmallModelComparison.rawToFrame_unit] at hs
  have hi : (eS).symm ((D).unit (MvPolynomial.X (j, i))) =
      principalCompletionUnitRingHom RS (p : RS)
        (PDSmallRawEnvelope.unit r n (MvPolynomial.X (j, i))) := by
    apply (eS).injective
    rw [AlgEquiv.apply_symm_apply, hs]
  rw [coefficientMap_eq_model]
  change (eT) ((coeff) ((eS).symm ((D).unit (MvPolynomial.X (j, i))))) = _
  rw [hi]
  have ht := pdModelBaseChange_unit p k l r ⦋n⦌
    (PDSmallRawEnvelope.unit r n (MvPolynomial.X (j, i)))
  change (coeff) (principalCompletionUnitRingHom RS (p : RS) _) =
    principalCompletionUnitRingHom RT (p : RT) (pdRawCoefficients k l r n _) at ht
  rw [ht, PDSmallModelComparison.termEquiv_unit, PDSmallRawEnvelope.unit_X,
    pdRawCoefficients_copy k l r ⦋n⦌ j.down i,
    ← PDSmallRawEnvelope.unit_X (k := l) r n (j, i),
    PDSmallModelComparison.rawToFrame_unit]

/-- 分冪枠の係数変更は基底の構造射と厳密に可換。 -/
theorem coefficientMap_base :
    (g).comp (algebraMap k (D).carrier) =
      (algebraMap l (E).carrier).comp (algebraMap k l) := by
  apply RingHom.ext
  intro x
  rw [coefficientMap_eq_model]
  change (eT) ((coeff) ((eS).symm (algebraMap k (D).carrier x))) = _
  rw [AlgEquiv.commutes]
  have h := ConcreteCategory.congr_hom (Under.w ((pdModelBaseChange p k l r).app ⦋n⦌)) x
  change (coeff) (algebraMap k (pdTerm p k r n) x) =
    algebraMap l (pdTerm p l r n) (algebraMap k l x) at h
  rw [h]
  exact (eT).commutes _

variable (hγ : γ.IsDPMorphism ε (algebraMap k l))

include hγ in
/-- 完備模型の実際の係数変更は、分冪枠の分冪構造を保つ。 -/
theorem coefficientMap_isDPMorphism : (D).dividedPowers.IsDPMorphism (E).dividedPowers (g) := by
  let α : AdicCompletion (Ideal.span {(p : RS)}) RS →+* (E).carrier :=
    (eT).toRingHom.comp ((coeff).comp (cS).symm.toRingHom)
  have hu : α.comp ((PDSmallModelComparison.toAdicCompletion p k RS).toRingHom) =
      (PDSmallModelComparison.rawToFrame p l ε hpL hl hrL r hI n).toRingHom.comp
        (pdRawCoefficients k l r n).toRingHom := by
    apply RingHom.ext
    intro x
    change (eT) ((coeff) ((cS).symm
      ((PDSmallModelComparison.toAdicCompletion p k RS).toRingHom x))) = _
    rw [inverse_completion_unit (hrK := hrK)]
    have h := pdModelBaseChange_unit p k l r ⦋n⦌ x
    change (coeff) (principalCompletionUnitRingHom RS (p : RS) x) =
      principalCompletionUnitRingHom RT (p : RT) (pdRawCoefficients k l r n x) at h
    rw [h]
    exact PDSmallModelComparison.termEquiv_unit p l ε hpL hl hrL r hI n _
  let δ := PDSmallRawEnvelope.dividedPowers p r n γ hk hrK
  have hf : δ.IsDPMorphism (E).dividedPowers
      (α.comp ((PDSmallModelComparison.toAdicCompletion p k RS).toRingHom)) := by
    rw [hu]
    exact (PDSmallModelComparison.rawToFrame_isDPMorphism p l ε hpL hl hrL r hI n).comp _
      (pdRawCoefficients_isDPMorphism p r n γ ε hk hl hrK hrL hγ)
  have hRaw := PDSmallRawEnvelope.isRelativePDEnvelope p r n γ hk hrK
  let := (E).isEnvelope.complete
  have hα := PDAdicCompletion.isDPMorphism_of_comp p δ (hRaw.prime_mem p hpK)
    (E).dividedPowers α hf
  have hd : (D).dividedPowers.IsDPMorphism
      (PDAdicCompletion.dividedPowers p δ (hRaw.prime_mem p hpK))
      (dS).symm.toRingHom := by
    exact (D).isEnvelope.equiv_isDPMorphism (hRaw.complete p hpK)
  exact hα.comp _ hd

variable (Dk : DeltaStructure p k) (Dl : DeltaStructure p l)
variable (hlocalK : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : k))
variable (hlocalL : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : l))
variable (hφK : J.map Dk.frobeniusLift ≤ Ideal.span {(p : k)})
variable (hφL : I.map Dl.frobeniusLift ≤ Ideal.span {(p : l)})
variable (hfδ : Dk.IsDeltaHom Dl (algebraMap k l))

include hγ hfδ in
/-- 実際の小さい分冪模型の係数変更は、標準の結晶 δ 構造を保つ。 -/
theorem coefficientMap_isDeltaHom
    (hD : Function.Injective (fun x : (D).carrier => (p : (D).carrier) * x))
    (hE : Function.Injective (fun x : (E).carrier => (p : (E).carrier) * x)) :
    (pdEnvelopeCrystalline Dk γ D hD hlocalK hφK).deltaStructure.IsDeltaHom
      (pdEnvelopeCrystalline Dl ε E hE hlocalL hφL).deltaStructure (g) := by
  apply pdEnvelopeCrystalline_coefficient_isDeltaHom Dk Dl γ ε D E hD hE
    hlocalK hlocalL hφK hφL (algebraMap k l) hfδ (g)
    (coefficientMap_base p k l γ ε hpK hpL hk hl hrK hrL r n hJ hI)
    (coefficientMap_isDPMorphism p k l γ ε hpK hpL hk hl hrK hrL r n hJ hI hγ) id
  rintro ⟨j, i⟩
  exact coefficientMap_variable p k l γ ε hpK hpL hk hl hrK hrL r n hJ hI j i

end SerrePositivity.BhattScholze.Prismatic.PDSmallCoefficientComparison
