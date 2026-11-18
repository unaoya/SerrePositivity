module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.HorizontalBoundary
public import Mathlib.Data.Fintype.BigOperators
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalEndpointSum

/-!
# 一般の単体集合の水平始端・終端の境界和

概要：Berger–Fresse §1.1.3 の水平な始端と終端の面の和を小さい shuffle の和に直す。
方針：固定位置への水平辺の挿入の全単射と符号つき面の等式を用いる。
規約：第一の入力の次数は p+1 から p に下がる。
使われ方：内部の水平面の和と合わせて第一の入力の微分の全項を得る。
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

/-- 概要：水平始端の面の和は第一の入力の最初の面の shuffle である（Berger–Fresse §1.1.3）。
方針：先頭への水平辺の挿入で添字替えして符号つき面の比較を使う。
規約：始端の境界符号と shuffle の符号の変化はともに 1 である。
使われ方：Leibniz 則の第一の入力の最初の境界項の和を同定する。 -/
lemma sum_horizontal_first_face (X Y : SSet.{0}) {p q : ℕ}
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    ∑ s : {s : ShufflePath (p + 1) q // 0 ∈ s.val},
      (s.val.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
        ((X ⊗ Y).map (horizontalFirstFaceMap p q).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s.val x y)) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q (X.δ 0 x) y := by
  classical
  let e := horizontalInsertionEquiv p q 0
  rw [← e.sum_comp]
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.value]
  apply Finset.sum_congr rfl
  intro s _
  have h := _root_.SerrePositivity.SimplicialChains.Shuffle.shuffle_horizontal_first_face_signed A X Y (e s).val (e s).property x y
  have hdel : (horizontalInsertionEquiv p q 0).symm ⟨(e s).val, (e s).property⟩ = s :=
    e.symm_apply_apply s
  rw [hdel] at h
  exact h

/-- 概要：水平終端の面の和は第一の入力の最後の面の shuffle である（Berger–Fresse §1.1.3）。
方針：終端への水平辺の挿入で添字替えして符号つき面の比較を使う。
規約：a は最後の辺であり、入力の境界符号は (−1)^(p+1) である。
使われ方：Leibniz 則の第一の入力の最後の境界項の和を同定する。 -/
lemma sum_horizontal_last_face (X Y : SSet.{0}) {p q : ℕ}
    (a : Fin (p + 1 + q)) (hlast : a.val + 1 = p + 1 + q)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    ∑ s : {s : ShufflePath (p + 1) q // a ∈ s.val},
      (-1 : ℤ) ^ (p + 1 + q) • (s.val.sign : ℤ) •
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
          ((X ⊗ Y).map (horizontalFaceMap p q a).op
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s.val x y)) =
      (-1 : ℤ) ^ (p + 1) •
        _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q (X.δ (Fin.last (p + 1)) x) y := by
  classical
  let e := horizontalInsertionEquiv p q a
  rw [← e.sum_comp]
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.value, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have h := _root_.SerrePositivity.SimplicialChains.Shuffle.shuffle_horizontal_last_face_signed A X Y (e s).val a (e s).property hlast x y
  have hdel : (horizontalInsertionEquiv p q a).symm ⟨(e s).val, (e s).property⟩ = s :=
    e.symm_apply_apply s
  rw [hdel, hlast] at h
  exact h

end SerrePositivity.SimplicialChains.Shuffle
