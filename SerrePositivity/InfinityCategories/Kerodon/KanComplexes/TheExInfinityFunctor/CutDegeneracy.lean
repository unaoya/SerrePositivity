module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.DegeneracyFibers
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionCommutation

/-!
# 切断した拡張退化の生成元上の式

概要：拡張退化の後で同じ閾値に切断した像を計算する。
方針：特別な頂点を分け、それ以外では通常の退化の不等式を使う。
規約：Moss 2020 Lemma 26 (8)・(9) の補助。
使われ方：通常の退化との交換を singleton 上で検証する。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder

/--
概要：切断後の拡張退化は閾値以下では singleton、その先では初期区間を与える。
方針：特別な頂点での初期区間の式と、残りの頂点での退化の比較式を合わせる。
規約：Moss 2020 Lemma 26 (8)・(9) の生成元上の共通の式。
使われ方：切断した拡張退化と通常の退化の合成則。
-/
theorem finiteChainCutDegeneracy_singleton (n : ℕ) (k : Fin (n + 1))
    (i : ULift.{u} (Fin (n + 2))) :
    finiteChainCut n (ULift.up k) (finiteChainDegeneracy n k (finiteChainSingleton i)) =
      if i ≤ ULift.up k.castSucc then finiteChainSingleton (liftedDegeneracy n k i)
      else finiteChainInitialSegment n (liftedDegeneracy n k i) := by
  rw [finiteChainDegeneracy_singleton]
  by_cases hi : i = ULift.up k.succ
  · subst i
    rw [ite_eq_left rfl, finiteChainCut_initialSegment, liftedDegeneracy_succ,
      ite_eq_right (show ¬ (ULift.up k.succ : ULift.{u} (Fin (n + 2))) ≤ ULift.up k.castSucc by
        change ¬ k.val + 1 ≤ k.val
        omega)]
  · rw [ite_eq_right hi, finiteChainCut_singleton]
    exact if_congr (liftedDegeneracy_le_iff_of_ne n k k le_rfl i hi) rfl rfl

/--
概要：後ろの通常の退化は小さい閾値との比較を保つ。
方針：predAbove の自然数の値を場合分けして比較する。
規約：Moss 2020 Lemma 26 (9)、k≤h。
使われ方：singleton と初期区間の場合分けの一致。
-/
theorem liftedDegeneracy_le_castSucc_iff (n : ℕ) (k h : Fin (n + 1)) (hkh : k ≤ h)
    (i : ULift.{u} (Fin (n + 3))) :
    liftedDegeneracy (n + 1) h.succ i ≤ ULift.up k.castSucc ↔
      i ≤ ULift.up k.castSucc.castSucc := by
  change (liftedDegeneracy (n + 1) h.succ i).down.val ≤ k.val ↔ i.down.val ≤ k.val
  rw [liftedDegeneracy_val]
  have hk : k.val ≤ h.val := hkh
  simp only [Fin.val_succ]
  split_ifs <;> omega

/--
概要：前側の通常の退化では閾値が一つ下がる。
方針：predAbove の自然数の値を場合分けして比較する。
規約：Moss 2020 Lemma 26 (8)、h≤k。
使われ方：singleton と初期区間の場合分けの一致。
-/
theorem liftedDegeneracy_le_succ_iff (n : ℕ) (h k : Fin (n + 1)) (hhk : h ≤ k)
    (i : ULift.{u} (Fin (n + 3))) :
    liftedDegeneracy (n + 1) h.castSucc i ≤ ULift.up k.castSucc ↔
      i ≤ ULift.up k.succ.castSucc := by
  change (liftedDegeneracy (n + 1) h.castSucc i).down.val ≤ k.val ↔ i.down.val ≤ k.val + 1
  rw [liftedDegeneracy_val]
  have hk : h.val ≤ k.val := hhk
  simp only [Fin.val_castSucc]
  split_ifs <;> omega

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
