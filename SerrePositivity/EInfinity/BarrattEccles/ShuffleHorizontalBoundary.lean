module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalSign
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleFirstFace

/-!
# 水平境界の符号つき正規化生成元

概要：Berger–Fresse §1.1.3 の水平面と両端の面について符号込みの鎖の等式を与える。
方針：単体の面の比較と shuffle 置換の signature の比較を組み合わせる。
規約：第一の入力の境界の符号に追加の Koszul 符号はない。
使われ方：shuffle の Leibniz 則の第一の入力の微分の各項を同定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：水平面の符号比較を整数で表す（Berger–Fresse §1.1.3）。
方針：単元群の符号公式を整数への包含で送る。
規約：入力の面の番号は辺 a の直後の水平座標である。
使われ方：整数のスカラー作用の係数を比較する。 -/
lemma horizontalBoundary_sign_int {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (ha : a ∈ s.val) :
    (-1 : ℤ) ^ (a.val + 1) * (s.sign : ℤ) =
      (-1 : ℤ) ^ (s.horizontal a.succ).val *
        (((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).sign : ℤ) := by
  exact congrArg (fun z : ℤˣ => (z : ℤ)) (horizontalBoundary_sign s a ha)

/-- 概要：水平始端を削除しても shuffle 符号は変わらない（Berger–Fresse §1.1.3）。
方針：辺の削除公式で辺の位置と直前の水平座標を零とする。
規約：最初の辺は水平である。
使われ方：第一の入力の最初の面の係数を計算する。 -/
lemma horizontalFirst_sign_int {p q : ℕ} (s : ShufflePath (p + 1) q)
    (h₀ : 0 ∈ s.val) :
    (s.sign : ℤ) = (((horizontalInsertionEquiv p q 0).symm ⟨s, h₀⟩).sign : ℤ) := by
  have h := sign_horizontalDeletion s 0 h₀
  have hh := s.horizontal_endpoints.1
  simpa only [Fin.castSucc_zero, Fin.val_zero, hh, Nat.zero_add, pow_zero, one_mul] using
    congrArg (fun z : ℤˣ => (z : ℤ)) h

/-- 概要：連続する水平辺の間の符号つき面は第一の入力の符号つき面に等しい（Berger–Fresse §1.1.3）。
方針：単体の面の一致の後、整数の符号比較をスカラーの積へ適用する。
規約：水平面の次数移送には horizontalFaceMap を使う。
使われ方：Leibniz 則の内部の水平面の各項を同定する。 -/
lemma shuffle_horizontal_face_signed (A : Type u) [CommRing A]
    (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a b : Fin (p + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    (-1 : ℤ) ^ (a.val + 1) • (s.sign : ℤ) • normalizedGenerator A (m + n) (p + q)
        ((simplicial (m + n)).map (horizontalFaceMap p q a).op
          (shuffleSimplex m n i (p := p + 1) (q := q) s x y)) =
      (-1 : ℤ) ^ (s.horizontal a.succ).val •
        (((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).sign : ℤ) •
          normalizedGenerator A (m + n) (p + q)
            (shuffleSimplex m n i (p := p) (q := q)
              ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩)
              ((simplicial (m + 1)).δ (s.horizontal a.succ) x) y) := by
  rw [shuffleSimplex_horizontal_face m n i s a b hab ha hb x y]
  simp only [smul_smul]
  rw [horizontalBoundary_sign_int s a ha]

/-- 概要：水平始端の符号つき面は第一の入力の最初の面を用いる（Berger–Fresse §1.1.3）。
方針：始端の単体の等式と始端の符号の保存を使う。
規約：最初の面の境界符号は 1 である。
使われ方：Leibniz 則の第一の入力の最初の境界項を同定する。 -/
lemma shuffle_horizontal_first_face_signed (A : Type u) [CommRing A]
    (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ} (s : ShufflePath (p + 1) q)
    (h₀ : 0 ∈ s.val)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    (s.sign : ℤ) • normalizedGenerator A (m + n) (p + q)
        ((simplicial (m + n)).map (horizontalFirstFaceMap p q).op
          (shuffleSimplex m n i (p := p + 1) (q := q) s x y)) =
      (((horizontalInsertionEquiv p q 0).symm ⟨s, h₀⟩).sign : ℤ) •
        normalizedGenerator A (m + n) (p + q)
          (shuffleSimplex m n i (p := p) (q := q)
            ((horizontalInsertionEquiv p q 0).symm ⟨s, h₀⟩)
            ((simplicial (m + 1)).δ 0 x) y) := by
  rw [shuffleSimplex_horizontal_first_face m n i s h₀ x y, horizontalFirst_sign_int s h₀]

/-- 概要：水平終端の符号つき面は第一の入力の最後の面を用いる（Berger–Fresse §1.1.3）。
方針：終端の水平座標を最後の頂点と同定して水平面の符号公式を使う。
規約：第一の入力の最後の面の境界符号は (−1)^(p+1) である。
使われ方：Leibniz 則の第一の入力の最後の境界項を同定する。 -/
lemma shuffle_horizontal_last_face_signed (A : Type u) [CommRing A]
    (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (ha : a ∈ s.val) (hlast : a.val + 1 = p + 1 + q)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    (-1 : ℤ) ^ (a.val + 1) • (s.sign : ℤ) • normalizedGenerator A (m + n) (p + q)
        ((simplicial (m + n)).map (horizontalFaceMap p q a).op
          (shuffleSimplex m n i (p := p + 1) (q := q) s x y)) =
      (-1 : ℤ) ^ (p + 1) •
        (((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).sign : ℤ) •
          normalizedGenerator A (m + n) (p + q)
            (shuffleSimplex m n i (p := p) (q := q)
              ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩)
              ((simplicial (m + 1)).δ (Fin.last (p + 1)) x) y) := by
  have hend : a.succ = Fin.last (p + 1 + q) := Fin.ext hlast
  have hsign := horizontalBoundary_sign_int s a ha
  rw [hend, s.horizontal_endpoints.2] at hsign
  rw [shuffleSimplex_horizontal_last_face m n i s a ha hlast x y]
  simp only [smul_smul]
  rw [hsign]
  simp only [Fin.val_last]

end SerrePositivity.EInfinity.BarrattEccles
