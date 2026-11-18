module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.VerticalBoundary
public import Mathlib.Data.Fintype.BigOperators
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalEndpointSum

/-!
# 一般の単体集合の垂直始端・終端の境界和

概要：Berger–Fresse §1.1.3 の垂直な始端と終端の面の和を小さい shuffle の和に直す。
方針：固定した位置への垂直辺の挿入の全単射と、符号つき面の等式を用いる。
規約：始端と終端は別の有限和で扱い、垂直次数は q+1 から q に下がる。
使われ方：内部の垂直面の和と合わせて第二の入力の微分の全項を得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：垂直始端の面の和は第二の入力の最初の面の shuffle である（Berger–Fresse §1.1.3）。
方針：先頭への垂直辺の挿入で添字替えして符号つき面の比較を使う。
規約：第二の入力の微分の Koszul 符号 (−1)^p を含む。
使われ方：Leibniz 則の第二の入力の最初の境界項の有限和を同定する。 -/
lemma sum_vertical_first_face (X Y : SSet.{0}) {p q : ℕ}
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    ∑ s : {s : ShufflePath p (q + 1) // 0 ∉ s.val},
      (s.val.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
        ((X ⊗ Y).δ 0
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) s.val x y)) =
      (-1 : ℤ) ^ p • _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x (Y.δ 0 y) := by
  classical
  let e := verticalInsertionEquiv p q 0
  rw [← e.sum_comp]
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.value, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have h := _root_.SerrePositivity.SimplicialChains.Shuffle.shuffle_vertical_first_face_signed A X Y (e s).val (e s).property x y
  have hdel : (verticalInsertionEquiv p q 0).symm ⟨(e s).val, (e s).property⟩ = s :=
    e.symm_apply_apply s
  rw [hdel] at h
  exact h

/-- 概要：垂直終端の面の和は第二の入力の最後の面の shuffle である（Berger–Fresse §1.1.3）。
方針：終端への垂直辺の挿入で添字替えして符号つき面の比較を使う。
規約：境界符号 (−1)^(q+1) と Koszul 符号 (−1)^p を含む。
使われ方：Leibniz 則の第二の入力の最後の境界項の有限和を同定する。 -/
lemma sum_vertical_last_face (X Y : SSet.{0}) {p q : ℕ}
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    ∑ s : {s : ShufflePath p (q + 1) // Fin.last (p + q) ∉ s.val},
      (-1 : ℤ) ^ (p + (q + 1)) • (s.val.sign : ℤ) •
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
          ((X ⊗ Y).δ (Fin.last (p + q)).succ
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) s.val x y)) =
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ (q + 1) •
        _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x (Y.δ (Fin.last (q + 1)) y) := by
  classical
  let e := verticalInsertionEquiv p q (Fin.last (p + q))
  rw [← e.sum_comp]
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.value, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have h := _root_.SerrePositivity.SimplicialChains.Shuffle.shuffle_vertical_last_face_signed A X Y (e s).val (Fin.last (p + q))
    (e s).property (by simp only [Fin.val_last]; omega) x y
  have hdel : (verticalInsertionEquiv p q (Fin.last (p + q))).symm
      ⟨(e s).val, (e s).property⟩ = s := e.symm_apply_apply s
  rw [hdel] at h
  have hpow : (-1 : ℤ) ^ ((Fin.last (p + q)).val + 1) =
      (-1 : ℤ) ^ (p + (q + 1)) := congrArg (fun k => (-1 : ℤ) ^ k) (by
    simp only [Fin.val_last]
    omega)
  rw [hpow] at h
  exact h

end SerrePositivity.SimplicialChains.Shuffle
