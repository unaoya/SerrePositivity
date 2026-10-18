module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalCorner
public import Mathlib.Data.Fintype.BigOperators

/-!
# 内部の水平面の有限和の添字替え

概要：Berger–Fresse §1.1.3 の内部の水平面の和を第一の入力の内部の境界和と比較する。
方針：角の全単射を用い、各項の符号つき面の等式と欠落頂点の番号を代入する。
規約：始端・終端は含めず、入力の内部面は Fin p の番号 j に対して j+1 とする。
使われ方：shuffle の Leibniz 則の第一の入力の内部微分を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：内部の水平角に対応する符号つき正規化境界項（Berger–Fresse §1.1.3）。
方針：二辺の間の頂点を削除して shuffle 符号と境界符号を掛ける。
規約：面写像の次数移送には horizontalFaceMap を使う。
使われ方：内部の水平角の全体にわたる和の被加数となる。 -/
def horizontalCornerTerm (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌)
    (c : HorizontalCorner p q) : (normalizedChains A (m + n)).X (p + q) :=
  (-1 : ℤ) ^ (c.val.2.val + 1) • (c.val.1.sign : ℤ) •
    normalizedGenerator A (m + n) (p + q)
      ((simplicial (m + n)).map
        (horizontalFaceMap p q (Fin.cast (by omega) c.val.2.castSucc)).op
        (shuffleSimplex m n i (p := p + 1) (q := q) c.val.1 x y))

/-- 概要：水平角の添字替えは第一の入力の内部面の番号と符号を保存する（Berger–Fresse §1.1.3）。
方針：水平辺を挿入した角へ符号つき面の比較を適用し、昇順の辺番号を欠落頂点へ移す。
規約：入力の内部面の番号は j.succ.castSucc である。
使われ方：全単射による有限和の添字替えの各項の等式を与える。 -/
lemma horizontalCornerTerm_indexed (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌)
    (s : ShufflePath p q) (j : Fin p) :
    horizontalCornerTerm A m n i x y
        (horizontalCornerEquiv p q (horizontalMarkedEdgeEquiv p q (s, j))) =
      (-1 : ℤ) ^ (j.val + 1) • (s.sign : ℤ) •
        normalizedGenerator A (m + n) (p + q)
          (shuffleSimplex m n i (p := p) (q := q) s
            ((simplicial (m + 1)).δ j.succ.castSucc x) y) := by
  let v := horizontalMarkedEdgeEquiv p q (s, j)
  let c := horizontalCornerEquiv p q v
  let a := Fin.cast (by omega : p + q + 1 = p + 1 + q) v.val.2.castSucc
  let b := Fin.cast (by omega : p + q + 1 = p + 1 + q) v.val.2.succ
  have hcoord : c.val.1.horizontal a.succ = j.succ.castSucc := by
    apply Fin.ext
    have h := horizontalCornerEquiv_horizontal v
    change (c.val.1.horizontal a.succ).val = (s.horizontal v.val.2.castSucc).val + 1 at h
    erw [horizontalMarkedEdgeEquiv_horizontal s j] at h
    exact h
  have hdel : (horizontalInsertionEquiv p q a).symm ⟨c.val.1, c.property.1⟩ = s :=
    (horizontalInsertionEquiv p q a).symm_apply_apply s
  change (-1 : ℤ) ^ (v.val.2.val + 1) • (c.val.1.sign : ℤ) •
    normalizedGenerator A (m + n) (p + q)
      ((simplicial (m + n)).map (horizontalFaceMap p q a).op
        (shuffleSimplex m n i (p := p + 1) (q := q) c.val.1 x y)) = _
  erw [shuffle_horizontal_face_signed A m n i c.val.1 a b rfl
    c.property.1 c.property.2 x y, hdel, hcoord]
  simp only [Fin.val_castSucc, Fin.val_succ]

/-- 概要：内部の水平角の境界和は第一の入力の内部境界を用いた shuffle の和に等しい（Berger–Fresse §1.1.3）。
方針：角と小さい経路・水平辺番号の全単射で有限和を添字替えし、各項の等式を使う。
規約：第一の入力の微分には追加の Koszul 符号を付けない。
使われ方：Leibniz 則の第一の入力の内部微分の寄与を同定する。 -/
lemma sum_horizontalCornerTerm (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    ∑ c : HorizontalCorner p q, horizontalCornerTerm A m n i x y c =
      ∑ s : ShufflePath p q, ∑ j : Fin p,
        (-1 : ℤ) ^ (j.val + 1) • (s.sign : ℤ) •
          normalizedGenerator A (m + n) (p + q)
            (shuffleSimplex m n i (p := p) (q := q) s
              ((simplicial (m + 1)).δ j.succ.castSucc x) y) := by
  classical
  let e := (horizontalMarkedEdgeEquiv p q).trans (horizontalCornerEquiv p q)
  rw [← e.sum_comp (horizontalCornerTerm A m n i x y), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro j _
  exact horizontalCornerTerm_indexed A m n i x y s j

end SerrePositivity.EInfinity.BarrattEccles
