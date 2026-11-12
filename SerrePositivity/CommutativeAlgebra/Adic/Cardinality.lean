module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# 古典的なイデアル進完備化の濃度評価

## 概要
完備化の各有限段で代表元を選び、元の加群の可算列へ単射を作る。

## 方針
代表元の一致から各剰余成分の一致を得て、完備化の ext を使う。

## 規約
有限生成性・分離性・Noether 性は不要。R と M は同じ宇宙。

## 使われ方
Berthelot I.2.3.1 の p 完備分冪包と affine 結晶サイトの cutoff。
-/

public noncomputable section
universe u
namespace SerrePositivity
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

/-- 古典的な完備化の濃度は元の加群の可算列の濃度以下。 -/
theorem adicCompletion_cardinal_le :
    Cardinal.mk (AdicCompletion I M) ≤ Cardinal.mk M ^ Cardinal.aleph0 := by
  let lift : AdicCompletion I M → ℕ → M := fun x n =>
    ((I ^ n • (⊤ : Submodule R M)).mkQ_surjective (x.val n)).choose
  have hinj : Function.Injective lift := by
    intro x y h
    apply AdicCompletion.ext
    intro n
    have hx := ((I ^ n • (⊤ : Submodule R M)).mkQ_surjective (x.val n)).choose_spec
    have hy := ((I ^ n • (⊤ : Submodule R M)).mkQ_surjective (y.val n)).choose_spec
    exact hx.symm.trans ((congrArg (I ^ n • (⊤ : Submodule R M)).mkQ
      (congrFun h n)).trans hy)
  simpa only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_uzero,
    Cardinal.mk_nat, Cardinal.lift_aleph0]
    using Cardinal.mk_le_of_injective hinj

/-- 可算冪で閉じた濃度の上限は、古典的な完備化でも保たれる。 -/
theorem adicCompletion_cardinal_le_of_closed (κ : Cardinal.{u})
    (hκ : κ ^ Cardinal.aleph0 = κ) (hM : Cardinal.mk M ≤ κ) :
    Cardinal.mk (AdicCompletion I M) ≤ κ :=
  (adicCompletion_cardinal_le (M := M) I).trans
    ((Cardinal.power_le_power_right hM).trans_eq hκ)

end SerrePositivity
