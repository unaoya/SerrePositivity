module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneOmegaDimensionShift
public import SerrePositivity.EInfinity.PowerOperation.PointedNaturalIsoDetection

/-!
# 指定 Γ 構造射の標準基点での Ω 条件を零次数へ帰着する

DAG XIII §2.2 の Ω 比較への前段。実際のシフトの逆同型と恒等 cone の
接続同値を使う。零次数の条件を証明済みとは仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (pointedHomotopyMap)
variable (A : Type u) [CommRing A]

/-- 零次数が全複体で全単射なら、同じ指定射は標準基点で全次数の全単射。 -/
lemma gammaAdjointSuspension_bijective_of_zero
    (h0 : ∀ M : Complex A,
      Function.Bijective (pointedHomotopyMap 0 ((gammaAdjointSuspension A).app M)))
    (M : Complex A) (n : ℕ) :
    Function.Bijective (pointedHomotopyMap n ((gammaAdjointSuspension A).app M)) := by
  induction n generalizing M with
  | zero => exact h0 M
  | succ n ih =>
    let e : (M⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ M :=
      (shiftFunctorCompIsoId (Complex A) (-1 : ℤ) (1 : ℤ) (by decide)).app M
    have h := (gammaAdjointSuspension_bijective_iff_shift A (M⟦(-1 : ℤ)⟧) n).mp
      (ih (M⟦(-1 : ℤ)⟧))
    exact (pointedNatural_bijective_iff_of_iso (gammaPointedFunctor A) (gammaLoopFunctor A)
      (gammaAdjointSuspension A) e (n + 1)).mp h

end SerrePositivity.EInfinity.PowerOperation
