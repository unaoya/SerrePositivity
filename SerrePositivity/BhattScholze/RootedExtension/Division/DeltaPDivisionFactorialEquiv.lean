module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialStable
public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionRawEmbedding

/-! # 正則一元raw包と具体的階乗生成部分環の標準同型

単射性の中間仮定を明示する。導来pushout比較・分冪包普遍性は別工程。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
local notation "ys" => fun _ : σ ↦ y
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "L₀" => Localization.Away (p : A)
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀

/-- 正則一元raw包と局所化内の具体的階乗生成部分環の標準環同型。 -/
def deltaPDivisionRawFactorialEquiv : B₀ ≃+* pDivisionFactorialSubring p ys :=
  (deltaPDivisionRawRangeEquiv (σ := σ) D y hpA hg v hv hy).trans
    (RingEquiv.subringCongr (pDivisionFactorialSubring_eq_raw_range hlocal D ys).symm)

include hpA hg hv hy hlocal

/-- 同型の値は既存の具体的δ評価そのもの。 -/
theorem deltaPDivisionRawFactorialEquiv_apply (b : B₀) :
    (deltaPDivisionRawFactorialEquiv D y hpA hg v hv hy hlocal b : L₀) =
      deltaPDivisionToAway D a₀ b := by
  rw [deltaPDivisionRawFactorialEquiv, RingEquiv.trans_apply, RingEquiv.coe_subringCongr_apply]
  exact deltaPDivisionRawRangeEquiv_apply (σ := σ) D y hpA hg v hv hy b

/-- 同型は元のAからの基底標準射を保つ。 -/
theorem deltaPDivisionRawFactorialEquiv_coeff (r : A) :
    (deltaPDivisionRawFactorialEquiv D y hpA hg v hv hy hlocal (j₀ r) : L₀) =
      algebraMap A L₀ r := by
  rw [deltaPDivisionRawFactorialEquiv_apply]
  exact RingHom.congr_fun (deltaPDivisionToAway_spec D a₀).2.1 r

/-- 同型はraw包内の階乗分母を局所化内の標準階乗分母へ送る。 -/
theorem deltaPDivisionRawFactorialEquiv_factorial (s : σ) (n : ℕ) :
    (deltaPDivisionRawFactorialEquiv D y hpA hg v hv hy hlocal
      (deltaPDivisionRawFactorialQuotient D ys hlocal s n) : L₀) =
      pDivisionFactorialValue p ys s n := by
  rw [deltaPDivisionRawFactorialEquiv_apply]
  exact deltaPDivisionToAway_factorialQuotient D ys hlocal s n

end SerrePositivity.BhattScholze
