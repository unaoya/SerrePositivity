module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.WeightedTensorFamily

/-!
# 入力の重みを保つ射とテンソル冪

## 概要
Berger–Moerdijk §1 の反復テンソル関手は指定された基底の重みの上限を保つ。

## 方針
零乗は単位基底とし、後続の乗数では二つの重み保存の射をテンソルする。

## 規約
入力と出力の基底の添字は異なってよい。

## 使われ方
セル段の包含で生成元の語の総重みが増えないことの証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexWeightBasis
open CategoryTheory MonoidalCategory DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A] {K L : Complex A}

/-- Taking any tensor power preserves the weight bound of a bound-preserving input map. -/
lemma Preserves.powerMap {b : ComplexWeightBasis K} {c : ComplexWeightBasis L}
    {f : K ⟶ L} (hf : b.Preserves c f) (n : ℕ) :
    (b.power n).Preserves (c.power n) (TensorPowers.map f n) := by
  induction n with
  | zero => exact preserves_id unit
  | succ n ih =>
    rw [power_succ, power_succ]
    exact hf.tensor ih

end SerrePositivity.EInfinity.ComplexWeightBasis
