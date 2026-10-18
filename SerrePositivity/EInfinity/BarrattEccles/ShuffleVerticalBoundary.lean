module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalSign
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleFirstFace

/-!
# 垂直境界の符号つき正規化生成元

概要：Berger–Fresse §1.1.3 の垂直面と両端の面について符号込みの鎖の等式を与える。
方針：単体の面の比較と shuffle 置換の signature の比較を組み合わせる。
規約：境界と shuffle の符号は整数のスカラー作用として正規化鎖へ作用する。
使われ方：shuffle の Leibniz 則の第二の入力の微分の各項を同定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：垂直面の符号比較を整数で表す（Berger–Fresse §1.1.3）。
方針：単元群の符号公式を整数への包含で送る。
規約：第二の入力の境界には水平次数 p の Koszul 符号が付く。
使われ方：整数のスカラー作用の係数を比較する。 -/
lemma verticalBoundary_sign_int {p q : ℕ} (s : ShufflePath p (q + 1))
    (a : Fin (p + (q + 1))) (ha : a ∉ s.val) :
    (-1 : ℤ) ^ (a.val + 1) * (s.sign : ℤ) =
      (-1 : ℤ) ^ p * (-1 : ℤ) ^ (s.vertical a.succ).val *
        (((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).sign : ℤ) := by
  exact congrArg (fun z : ℤˣ => (z : ℤ)) (verticalBoundary_sign s a ha)

/-- 概要：垂直始端を削除すると shuffle 符号に (−1)^p が付く（Berger–Fresse §1.1.3）。
方針：辺の削除公式で先頭の辺の位置と直前の垂直座標を零とする。
規約：最初の辺は垂直である。
使われ方：第二の入力の最初の面の係数を計算する。 -/
lemma verticalFirst_sign_int {p q : ℕ} (s : ShufflePath p (q + 1))
    (h₀ : 0 ∉ s.val) :
    (s.sign : ℤ) = (-1 : ℤ) ^ p *
      (((verticalInsertionEquiv p q 0).symm ⟨s, h₀⟩).sign : ℤ) := by
  have h := sign_verticalDeletion s 0 h₀
  have hv := s.vertical_endpoints.1
  simpa only [Fin.castSucc_zero, Fin.val_zero, hv, Nat.add_zero, Nat.zero_add,
    Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using
    congrArg (fun z : ℤˣ => (z : ℤ)) h

/-- 概要：連続する垂直辺の間の符号つき面は第二の入力の符号つき面に等しい（Berger–Fresse §1.1.3）。
方針：単体の面の一致を使った後、整数の符号比較をスカラーの積へ適用する。
規約：第二の入力の微分には (−1)^p が付く。
使われ方：Leibniz 則の内部の垂直面の各項を同定する。 -/
lemma shuffle_vertical_face_signed (A : Type u) [CommRing A]
    (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ} (s : ShufflePath p (q + 1))
    (a b : Fin (p + (q + 1))) (hab : b.val = a.val + 1)
    (ha : a ∉ s.val) (hb : b ∉ s.val)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (-1 : ℤ) ^ (a.val + 1) • (s.sign : ℤ) • normalizedGenerator A (m + n) (p + q)
        ((simplicial (m + n)).δ a.succ
          (shuffleSimplex m n i (p := p) (q := q + 1) s x y)) =
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ (s.vertical a.succ).val •
        (((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).sign : ℤ) •
          normalizedGenerator A (m + n) (p + q)
            (shuffleSimplex m n i (p := p) (q := q)
              ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩) x
              ((simplicial n).δ (s.vertical a.succ) y)) := by
  rw [shuffleSimplex_vertical_face m n i s a b hab ha hb x y]
  simp only [smul_smul]
  rw [verticalBoundary_sign_int s a ha]
  rw [mul_assoc]

/-- 概要：垂直始端の符号つき面は第二の入力の最初の面を用いる（Berger–Fresse §1.1.3）。
方針：始端の単体の等式と垂直始端の符号公式を使う。
規約：最初の面の境界符号は 1 である。
使われ方：Leibniz 則の第二の入力の最初の境界項を同定する。 -/
lemma shuffle_vertical_first_face_signed (A : Type u) [CommRing A]
    (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ} (s : ShufflePath p (q + 1))
    (h₀ : 0 ∉ s.val)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (s.sign : ℤ) • normalizedGenerator A (m + n) (p + q)
        ((simplicial (m + n)).δ 0
          (shuffleSimplex m n i (p := p) (q := q + 1) s x y)) =
      (-1 : ℤ) ^ p • (((verticalInsertionEquiv p q 0).symm ⟨s, h₀⟩).sign : ℤ) •
        normalizedGenerator A (m + n) (p + q)
          (shuffleSimplex m n i (p := p) (q := q)
            ((verticalInsertionEquiv p q 0).symm ⟨s, h₀⟩) x ((simplicial n).δ 0 y)) := by
  erw [shuffleSimplex_vertical_first_face m n i s h₀ x y,
    verticalFirst_sign_int s h₀, smul_smul]

/-- 概要：垂直終端の符号つき面は第二の入力の最後の面を用いる（Berger–Fresse §1.1.3）。
方針：終端の座標を最後の頂点と同定して垂直面の符号公式を使う。
規約：第二の入力の最後の面の境界符号は (−1)^(q+1) である。
使われ方：Leibniz 則の第二の入力の最後の境界項を同定する。 -/
lemma shuffle_vertical_last_face_signed (A : Type u) [CommRing A]
    (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ} (s : ShufflePath p (q + 1))
    (a : Fin (p + (q + 1))) (ha : a ∉ s.val) (hlast : a.val + 1 = p + (q + 1))
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (-1 : ℤ) ^ (a.val + 1) • (s.sign : ℤ) • normalizedGenerator A (m + n) (p + q)
        ((simplicial (m + n)).δ a.succ
          (shuffleSimplex m n i (p := p) (q := q + 1) s x y)) =
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ (q + 1) •
        (((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).sign : ℤ) •
          normalizedGenerator A (m + n) (p + q)
            (shuffleSimplex m n i (p := p) (q := q)
              ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩) x
              ((simplicial n).δ (Fin.last (q + 1)) y)) := by
  have hend : a.succ = Fin.last (p + (q + 1)) := Fin.ext hlast
  have hsign := verticalBoundary_sign_int s a ha
  rw [hend, s.vertical_endpoints.2] at hsign
  rw [shuffleSimplex_vertical_last_face m n i s a ha hlast x y]
  simp only [smul_smul]
  rw [hsign, mul_assoc]
  simp only [Fin.val_last]

end SerrePositivity.EInfinity.BarrattEccles
