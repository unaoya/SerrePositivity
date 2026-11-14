module

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaBounds

/-!
# Čech–Alexander の変数集合と包の濃度

## 概要
全ての剰余環の元を各頂点の変数にしても、完備自由 δ 環は原典の cutoff に収まる。

## 方針
変数の有限積の濃度を無限基数で抑え、既存の完備自由 δ 環の可算冪の評価を使う。

## 規約
BS 著者版 Construction 4.18、濃度の決定 D16。元の環の大きさを縮めない。

## 使われ方
既存の affineBigCechTerm を指定した site の対象に入れる。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open Cardinal
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 概要：各元と有限個の頂点による完備自由 δ 環の濃度は cutoff 以下。
方針：変数の積と和を同じ無限基数で抑え、可算冪の単調性を使う。
規約：BS 著者版 Construction 4.18。使われ方：大きい枠の濃度の供給。 -/
theorem completedFreeDelta_cechIndex_mk_le_cutoff (P : OrientedPrism p A) (R : Type u) (n : ℕ) :
    Cardinal.mk (completedFreeDelta P (R × Fin (n + 1))) ≤ cutoff A R := by
  let k : Cardinal.{u} := Cardinal.mk A + Cardinal.mk R + ℵ₀
  have hA : Cardinal.mk A ≤ k := (self_le_add_right _ _).trans (self_le_add_right _ _)
  have hR : Cardinal.mk R ≤ k := (self_le_add_left _ _).trans (self_le_add_right _ _)
  have hN : ℵ₀ ≤ k := self_le_add_left _ _
  have hF : Cardinal.lift.{u} (Cardinal.mk (Fin (n + 1))) ≤ k :=
    (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0).trans hN
  have hS : Cardinal.mk (R × Fin (n + 1)) ≤ k := by
    simpa only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_uzero] using
      (mul_le_mul' hR hF).trans (Cardinal.mul_eq_self hN).le
  have hsum : Cardinal.mk A + Cardinal.mk (R × Fin (n + 1)) + ℵ₀ ≤ k := by
    apply (add_le_add (add_le_add hA hS) hN).trans
    rw [Cardinal.add_eq_self hN, Cardinal.add_eq_self hN]
  exact (cardinal_envelope_le P (R × Fin (n + 1))).trans
    (Cardinal.power_le_power_right hsum)

end SerrePositivity.BhattScholze.Prismatic
