module

public import SerrePositivity.BhattScholze.Delta.DeltaWittGhostFrobenius
public import SerrePositivity.BhattScholze.Delta.DeltaWittGhostLowCoefficients
public import Mathlib.RingTheory.WittVector.Identities

/-! # q(y)=0となる通常係数射に沿うφ(y)/pの具体的Witt解

終域にδ構造を要求しない。全Witt係数の除算方程式を証明する。
rawδ反復関係を消す通常評価への移送・分冪包比較は別工程。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (q : A →+* B) (y : A)

/-- 基底Witt元の像の係数を一段ずらした、具体的なp除算解候補。 -/
def deltaPDivisionWittResidueSolution : WittVector p B :=
  WittVector.mk p (fun n ↦ q ((deltaWittGhostVector D y).coeff (n + 1)))

/-- 解候補の全Witt係数の具体式。 -/
theorem deltaPDivisionWittResidueSolution_coeff (n : ℕ) :
    (deltaPDivisionWittResidueSolution D q y).coeff n =
      q ((deltaWittGhostVector D y).coeff (n + 1)) := rfl

/-- q(y)=0なら、Verschiebungで元の基底Witt元の像へ戻る。 -/
theorem deltaPDivisionWittResidueSolution_verschiebung (hqy : q y = 0) :
    WittVector.verschiebung (deltaPDivisionWittResidueSolution D q y) =
      WittVector.map q (deltaWittGhostVector D y) := by
  ext n
  cases n with
  | zero => rw [WittVector.verschiebung_coeff_zero, WittVector.map_coeff,
      deltaWittGhostVector_coeff_zero, hqy]
  | succ n => rw [WittVector.verschiebung_coeff_succ,
      deltaPDivisionWittResidueSolution_coeff, WittVector.map_coeff]

/-- 具体的候補はp*t=s(φ(y))という全Witt環内の方程式を満たす。 -/
theorem deltaPDivisionWittResidueSolution_mul
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqy : q y = 0) :
    (p : WittVector p B) * deltaPDivisionWittResidueSolution D q y =
      WittVector.map q (deltaWittGhostVector D (D.frobeniusLift y)) := by
  calc
    _ = WittVector.frobenius (WittVector.verschiebung
        (deltaPDivisionWittResidueSolution D q y)) := by
      rw [WittVector.frobenius_verschiebung, mul_comm]
    _ = WittVector.frobenius (WittVector.map q (deltaWittGhostVector D y)) := by
      rw [deltaPDivisionWittResidueSolution_verschiebung D q y hqy]
    _ = WittVector.map q (deltaWittGhostVector D (D.frobeniusLift y)) :=
      ((WittVector.frobenius_isPoly p).map q (deltaWittGhostVector D y)).symm.trans
        (congrArg (WittVector.map q) (deltaWittGhostVector_frobenius D hg y))

/-- pを基底のWitt切断で表しても同じ具体的除算方程式。 -/
theorem deltaPDivisionWittResidueSolution_mul_source_prime
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqy : q y = 0) :
    WittVector.map q (deltaWittGhostVector D (p : A)) * deltaPDivisionWittResidueSolution D q y =
      WittVector.map q (deltaWittGhostVector D (D.frobeniusLift y)) := by
  have he : WittVector.map q (deltaWittGhostVector D (p : A)) = (p : WittVector p B) := by
    change WittVector.map q (deltaWittGhostRingHom D hg (p : A)) = _
    rw [map_natCast, map_natCast]
  rw [he]
  exact deltaPDivisionWittResidueSolution_mul D q y hg hqy

/-- 元の係数から来る全Witt関係を一度に消す係数ごとの式。 -/
theorem deltaPDivisionWittResidueSolution_coordinate_relation
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqy : q y = 0) (n : ℕ) :
    (WittVector.map q (deltaWittGhostVector D (p : A)) *
      deltaPDivisionWittResidueSolution D q y).coeff n =
        q ((deltaWittGhostVector D (D.frobeniusLift y)).coeff n) := by
  have h := congrArg (fun w : WittVector p B ↦ w.coeff n)
    (deltaPDivisionWittResidueSolution_mul_source_prime D q y hg hqy)
  simpa only [WittVector.map_coeff] using h

/-- 源がp正則なら、解の第0係数は具体的にq(δy)。 -/
theorem deltaPDivisionWittResidueSolution_coeff_zero
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    (deltaPDivisionWittResidueSolution D q y).coeff 0 = q (D.delta y) := by
  rw [deltaPDivisionWittResidueSolution_coeff, Nat.zero_add,
    deltaWittGhostVector_coeff_one D hp]

end SerrePositivity.BhattScholze
