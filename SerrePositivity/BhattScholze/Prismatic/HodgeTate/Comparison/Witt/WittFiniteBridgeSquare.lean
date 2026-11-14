module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridge
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDPrismMaps
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigCrystalline
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigCrystalline
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.BigPDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigBridgeAffineFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittToSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameComparison
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# Witt の結晶の橋と枠の変更の可換性

## 概要
有限枠への結晶の橋と大きい枠への結晶の橋は、枠を移すと一致する。

## 方針
二つの合成は基底上で ψ に一致し、各頂点で同じ変数の p 乗を与える。

## 規約
固定した次数で環射の等式を示す。

## 使われ方
BS 著者版 Theorem 6.4 の結晶の橋の擬同型を有限枠に帰着する。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.WittFiniteBridge

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hloc : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable (hk : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal))
variable [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable (Q : Poly (A ⧸ P.ideal)) (n : ℕ)
variable {κ : Cardinal.{u}} (X : AffineEnvelopeTerm P Q.n n κ) (Y : BigCechTerm P Q n)

local notation "C" => (A ⧸ P.ideal)
local notation "W" => WittVector p C
local notation "γ" => wittPdStructure p C hpC hloc
local notation "hpW" => p_mem_wittPdIdeal p C
local notation "D₀" => PDCechNerve.term p γ hpW (smallResidue_ker P Q) (smallFrame P Q) n
local notation "D₁" => WittBigBridge.termAt P hpC hloc Q n
local notation "h₀" => regular P hpC hloc hk Q n
local notation "h₁" => WittBigBridge.regularAt P hpC hloc Q n
local notation "T" => WittBigBridge.prismAt P hpC hloc Q n
local notation "base" => WittBigBridge.targetBase P hpA hpC hloc Q n

private abbrev inclusion : (D₀).carrier →ₐ[W] (D₁).carrier :=
  WittToSmallFrame.frameInclusion P hpC hloc Q n

private theorem inclusion_delta :
    (wittPDEnvelopeCrystalline hpC hloc D₀ h₀).deltaStructure.IsDeltaHom (T).deltaStructure
      (inclusion P hpC hloc Q n).toRingHom := by
  apply wittPDEnvelopeCrystalline_isDeltaHom hpC hloc D₀ D₁ h₀ h₁
    (inclusion P hpC hloc Q n) (WittToSmallFrame.frameInclusion_dp P hpC hloc Q n)
    (fun s => (smallIndex P Q s.1, s.2))
  rintro ⟨j, i⟩
  exact WittToSmallFrame.frameInclusion_X P hpC hloc Q n j i

private def finiteToLargeAt : X.X.B →+* (D₁).carrier :=
  (inclusion P hpC hloc Q n).toRingHom.comp (existsUnique_at P hpA hpC hloc hk Q n X).choose

private def largeAt : X.X.B →+* (D₁).carrier :=
  (WittBigBridge.bridgeAt P hpA hpC hloc Q n Y).comp (affineToBig X Y)

private theorem largeAt_eq :
    largeAt P hpA hpC hloc Q n X Y = finiteToLargeAt P hpA hpC hloc hk Q n X := by
  let f := largeAt P hpA hpC hloc Q n X Y
  let g := finiteToLargeAt P hpA hpC hloc hk Q n X
  have hf := WittBigBridge.bridgeAt_spec P hpA hpC hloc Q n Y
  have hδf : X.X.Q.deltaStructure.IsDeltaHom (T).deltaStructure f :=
    hf.1.comp (affineToBig_spec X Y).1
  have hbf : f.comp X.X.toHom.toRingHom = (base).toRingHom := by
    change ((WittBigBridge.bridgeAt P hpA hpC hloc Q n Y).comp (affineToBig X Y)).comp
      X.X.toHom.toRingHom = _
    rw [RingHom.comp_assoc, (affineToBig_spec X Y).2.1, hf.2.1]
  have hgs := (existsUnique_at P hpA hpC hloc hk Q n X).choose_spec.1
  have hδg : X.X.Q.deltaStructure.IsDeltaHom (T).deltaStructure g :=
    (inclusion_delta P hpC hloc hk Q n).comp hgs.1
  have hbg : g.comp X.X.toHom.toRingHom = (base).toRingHom := by
    unfold g finiteToLargeAt
    rw [RingHom.comp_assoc, hgs.2.1]
    apply RingHom.ext
    intro x
    change inclusion P hpC hloc Q n (algebraMap W (D₀).carrier (psiRing P hpA x)) =
      algebraMap W (D₁).carrier (psiRing P hpA x)
    exact (inclusion P hpC hloc Q n).commutes _
  have hv (j : Fin Q.n) (i : Fin (n + 1)) :
      f (X.η (affineVariable P Q.n n j i)) = g (X.η (affineVariable P Q.n n j i)) := by
    change WittBigBridge.bridgeAt P hpA hpC hloc Q n Y
        (affineToBig X Y (X.η (affineVariable P Q.n n j i))) =
      inclusion P hpC hloc Q n ((existsUnique_at P hpA hpC hloc hk Q n X).choose
        (X.η (affineVariable P Q.n n j i)))
    rw [(affineToBig_spec X Y).2.2, hf.2.2, hgs.2.2, map_pow]
    exact congrArg (fun z : (D₁).carrier => z ^ p)
      (WittToSmallFrame.frameInclusion_X P hpC hloc Q n (ULift.up j) i).symm
  have hI : X.X.Q.ideal ≤ (T).ideal.comap f := by
    rw [X.envelope.ideal_eq, Ideal.span_singleton_le_iff_mem]
    change (f.comp (X.η.comp (completedFreeDeltaBase P _))) P.generator ∈ (T).ideal
    rw [X.base_eq, hbf]
    exact (base).map_generator_mem
  have hmod (j : Fin Q.n) (i : Fin (n + 1)) :
      Ideal.Quotient.mk (T).ideal (f (X.η (affineVariable P Q.n n j i))) =
        Ideal.Quotient.mk (T).ideal (f (X.η (affineVariable P Q.n n j 0))) := by
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    exact hI (affineTerm_difference_mem P X j i 0)
  apply (X.existsUnique_liftVariables (T) (base) _ hmod).unique
  · exact ⟨hδf, hbf, fun _ _ => rfl⟩
  · exact ⟨hδg, hbg, fun j i => (hv j i).symm⟩

/-- 小さい完備 Witt 模型の係数項を大きい枠に入れる。 -/
def finiteToBigRing : pdTerm p W Q.n n →ₐ[W] (WittBigCrystalline.term P hpC hloc Q n).carrier :=
  (inclusion P hpC hloc Q n).comp
    (PDSmallModelComparison.termEquiv p W γ hpW (wittComplete P hpC hk)
      (witt_mul_prime_injective p C hpC) Q.n (smallResidue_ker P Q) n).toAlgHom

/-- 有限枠の橋を大きい Witt 枠へ送ると、大きい枠での橋への制限を得る。 -/
theorem finiteBridgeAt_frame (x : X.X.B) :
    finiteToBigRing P hpC hloc hk Q n (finiteBridgeAt P hpA hpC hloc hk Q n X x) =
      WittBigBridge.fromAffineFrame P hpA hpC hloc X Y x := by
  let e := PDSmallModelComparison.termEquiv p W γ hpW (wittComplete P hpC hk)
    (witt_mul_prime_injective p C hpC) Q.n (smallResidue_ker P Q) n
  change inclusion P hpC hloc Q n
      (e (e.symm ((existsUnique_at P hpA hpC hloc hk Q n X).choose x))) =
    largeAt P hpA hpC hloc Q n X Y x
  rw [AlgEquiv.apply_symm_apply, largeAt_eq P hpA hpC hloc hk Q n X Y]
  rfl

end SerrePositivity.BhattScholze.Prismatic.WittFiniteBridge
