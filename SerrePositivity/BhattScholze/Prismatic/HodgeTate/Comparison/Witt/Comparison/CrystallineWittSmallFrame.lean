module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDEnvelopeAffineBridge
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittCoefficients
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDEnvelopeCrystalline
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDEnvelopeCrystalline
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialFunctor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# Witt 結晶基底上の小さい有限枠への橋

## 概要
Witt 結晶基底の有限 affine 枠から、小さい完備分冪枠への橋を固定する。

## 方針
既存の分冪包の結晶 prism と有限 affine 枠の普遍性を使う。
完備分冪模型の比較同型を通し、各頂点変数の p 乗の式を残す。

## 規約
係数環 C は p 正則かつ p 進完備で、p と素な自然数は単元。
Witt Frobenius 全体と係数を固定する頂点変数の p 乗の射を区別する。

## 使われ方
BS 著者版 Theorem 6.4 の最初の比較を結晶基底で検査する有限枠。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C]
variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable (hlocalC : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : C))
variable [hC : IsAdicComplete (Ideal.span {(p : C)}) C] (r n : ℕ)

local notation "W" => WittVector p C
local notation "Jw" => wittPdIdeal p C
local notation "γ" => wittPdStructure p C hpC hlocalC
local notation "s" => (fun j : ULift (Fin r) =>
  (MvPolynomial.X (ULift.down j) : MvPolynomial (Fin r) (W ⧸ Jw)))
local notation "hJ" => PDPolynomialFunctor.base_ker (J := Jw) (Poly.mk r : Poly W)
local notation "hpW" => p_mem_wittPdIdeal p C
local notation "hkW" => witt_isAdicComplete p C hpC
local notation "hrW" => witt_mul_prime_injective p C hpC

/-- Witt 結晶基底の小さい完備分冪枠。 -/
def crystallineWittSmallFrameTarget :
    CompletedPDEnvelopeData p γ (RingHom.ker (pdFrameEval (k := W) s n)) :=
  PDCechNerve.term p γ hpW hJ s n

local notation "E" => crystallineWittSmallFrameTarget p C hpC hlocalC r n

private def crystallineWittSmallFrameEquiv : pdTerm p W r n ≃ₐ[W] (E).carrier :=
  PDSmallModelComparison.termEquiv p W γ hpW hkW hrW r hJ n

include hC in
private theorem crystallineWittSmallFrame_regular :
    Function.Injective (fun x : (E).carrier => (p : (E).carrier) * x) := by
  let e := crystallineWittSmallFrameEquiv p C hpC hlocalC r n
  intro x y h
  apply e.symm.injective
  have h' := congrArg e.symm h
  simp only [map_mul, map_natCast] at h'
  apply principalCompletionH0_smul_injective_of_regular (pdRaw W r n) (p : pdRaw W r n)
    (PDSmallRawEnvelope.raw_regular p r n hrW)
  have h'' : p • (e.symm x : pdTerm p W r n) = p • (e.symm y : pdTerm p W r n) := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    exact h'
  simpa only [Nat.cast_smul_eq_nsmul] using h'' 

private def crystallineWittSmallFramePrism : OrientedPrism p (E).carrier :=
  wittPDEnvelopeCrystalline hpC hlocalC E (crystallineWittSmallFrame_regular p C hpC hlocalC r n)

local notation "T" => crystallineWittSmallFramePrism p C hpC hlocalC r n

omit hC in
private theorem crystallineWittSmallFrame_difference_mem (j : Fin r) (i : Fin (n + 1)) :
    (E).unit (MvPolynomial.X (ULift.up j, i)) -
      (E).unit (MvPolynomial.X (ULift.up j, 0)) ∈ (E).ideal := by
  unfold crystallineWittSmallFrameTarget
  rw [← PDCechNerve.augmentation_ker]
  apply RingHom.mem_ker.mpr
  rw [map_sub]
  change PDCechNerve.augmentation p γ hpW hJ s n
      (PDCechNerve.variableImage p γ hpW hJ s n (ULift.up j, i)) -
    PDCechNerve.augmentation p γ hpW hJ s n
      (PDCechNerve.variableImage p γ hpW hJ s n (ULift.up j, 0)) = 0
  rw [PDCechNerve.augmentation_variableImage, PDCechNerve.augmentation_variableImage, sub_self]

variable {κ : Cardinal.{u}} (V : AffineEnvelopeTerm (wittCrystallinePrism hpC) r n κ)

private def crystallineWittSmallFrameMap : V.X.B →+* (E).carrier :=
  pdEnvelopeAffineBridge γ r n E T
    (wittPDEnvelopeCrystalline_generator hpC hlocalC E _)
    (wittCrystallinePrism hpC) V
    (crystallineWittSmallFrame_difference_mem p C hpC hlocalC r n)
    (wittPDEnvelopeCrystallineBase hpC hlocalC E _)

/-- Witt 結晶基底の有限 affine 枠から、小さい完備分冪模型への橋。 -/
def crystallineWittSmallBridgeAt : V.X.B →+* pdTerm p W r n :=
  (crystallineWittSmallFrameEquiv p C hpC hlocalC r n).symm.toRingHom.comp
    (crystallineWittSmallFrameMap p C hpC hlocalC r n V)

private theorem crystallineWittSmallFrameMap_spec :
    V.X.Q.deltaStructure.IsDeltaHom (T).deltaStructure
        (crystallineWittSmallFrameMap p C hpC hlocalC r n V) ∧
      (crystallineWittSmallFrameMap p C hpC hlocalC r n V).comp V.X.toHom.toRingHom =
        algebraMap W (E).carrier ∧
      ∀ j i, crystallineWittSmallFrameMap p C hpC hlocalC r n V
        (V.η (affineVariable (wittCrystallinePrism hpC) r n j i)) =
          (E).unit (MvPolynomial.X (ULift.up j, i)) ^ p :=
  pdEnvelopeAffineBridge_spec γ r n E T
    (wittPDEnvelopeCrystalline_generator hpC hlocalC E _)
    (wittCrystallinePrism hpC) V
    (crystallineWittSmallFrame_difference_mem p C hpC hlocalC r n)
    (wittPDEnvelopeCrystallineBase hpC hlocalC E _)

/-- 小さい Witt 分冪模型の頂点変数。 -/
def crystallineWittSmallVariable (j : Fin r) (i : Fin (n + 1)) : pdTerm p W r n := by
  exact principalCompletionRingCatUnit p (CommRingCat.of (pdRaw W r n))
    (PDSmallRawEnvelope.unit r n (MvPolynomial.X (ULift.up j, i)))

private theorem crystallineWittSmallFrameEquiv_variable (j : Fin r) (i : Fin (n + 1)) :
    crystallineWittSmallFrameEquiv p C hpC hlocalC r n
        (crystallineWittSmallVariable p C r n j i) =
      (E).unit (MvPolynomial.X (ULift.up j, i)) := by
  exact (PDSmallModelComparison.termEquiv_unit p W γ hpW hkW hrW r hJ n _).trans
    (PDSmallModelComparison.rawToFrame_unit p W γ hpW hkW hrW r hJ n _)

/-- Witt 結晶基底上の小さい橋は各頂点変数を p 乗に送る。 -/
theorem crystallineWittSmallBridgeAt_variable (j : Fin r) (i : Fin (n + 1)) :
    crystallineWittSmallBridgeAt p C hpC hlocalC r n V
        (V.η (affineVariable (wittCrystallinePrism hpC) r n j i)) =
      crystallineWittSmallVariable p C r n j i ^ p := by
  apply (crystallineWittSmallFrameEquiv p C hpC hlocalC r n).injective
  change crystallineWittSmallFrameEquiv p C hpC hlocalC r n
    ((crystallineWittSmallFrameEquiv p C hpC hlocalC r n).symm
      (crystallineWittSmallFrameMap p C hpC hlocalC r n V
        (V.η (affineVariable (wittCrystallinePrism hpC) r n j i)))) = _
  rw [AlgEquiv.apply_symm_apply,
    (crystallineWittSmallFrameMap_spec p C hpC hlocalC r n V).2.2,
    map_pow, crystallineWittSmallFrameEquiv_variable]

/-- Witt 結晶基底上の小さい橋は基底の構造射を保つ。 -/
theorem crystallineWittSmallBridgeAt_base (a : W) :
    crystallineWittSmallBridgeAt p C hpC hlocalC r n V (V.X.toHom.toRingHom a) =
      algebraMap W (pdTerm p W r n) a := by
  have h := RingHom.congr_fun
    (crystallineWittSmallFrameMap_spec p C hpC hlocalC r n V).2.1 a
  change (crystallineWittSmallFrameEquiv p C hpC hlocalC r n).symm
    (crystallineWittSmallFrameMap p C hpC hlocalC r n V (V.X.toHom.toRingHom a)) = _
  simp only [RingHom.comp_apply] at h
  rw [h]
  exact (crystallineWittSmallFrameEquiv p C hpC hlocalC r n).symm.commutes a

end SerrePositivity.BhattScholze.Prismatic
