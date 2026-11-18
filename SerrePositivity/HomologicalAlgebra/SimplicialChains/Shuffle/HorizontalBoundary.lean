module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.EndpointFaces
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.Values
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalBoundary

/-!
# 一般 shuffle の水平境界の符号

概要：Berger–Fresse §1.1.3 の一般 shuffle の同方向の面を符号込みで比較する。
方針：一般の単体の面の一致と、既存の経路の整数符号公式を組み合わせる。
規約：任意の小さい単体集合と任意の可換係数環を扱う。
使われ方：shuffle の Leibniz 則の同方向の境界和。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

/-- 概要：連続する水平辺の間の符号つき面は第一の入力の符号つき面に等しい（Berger–Fresse §1.1.3）。
方針：単体の面の一致の後、整数の符号比較をスカラーの積へ適用する。
規約：水平面の次数移送には horizontalFaceMap を使う。
使われ方：Leibniz 則の内部の水平面の各項を同定する。 -/
lemma shuffle_horizontal_face_signed (A : Type u) [CommRing A]
    (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a b : Fin (p + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    (-1 : ℤ) ^ (a.val + 1) • (s.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
        ((X ⊗ Y).map (horizontalFaceMap p q a).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s x y)) =
      (-1 : ℤ) ^ (s.horizontal a.succ).val •
        (((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).sign : ℤ) •
          _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q)
              ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩)
              (X.δ (s.horizontal a.succ) x) y) := by
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.simplex_horizontal_face X Y s a b hab ha hb x y]
  simp only [smul_smul]
  rw [horizontalBoundary_sign_int s a ha]

/-- 概要：水平始端の符号つき面は第一の入力の最初の面を用いる（Berger–Fresse §1.1.3）。
方針：始端の単体の等式と始端の符号の保存を使う。
規約：最初の面の境界符号は 1 である。
使われ方：Leibniz 則の第一の入力の最初の境界項を同定する。 -/
lemma shuffle_horizontal_first_face_signed (A : Type u) [CommRing A]
    (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath (p + 1) q)
    (h₀ : 0 ∈ s.val)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    (s.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
        ((X ⊗ Y).map (horizontalFirstFaceMap p q).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s x y)) =
      (((horizontalInsertionEquiv p q 0).symm ⟨s, h₀⟩).sign : ℤ) •
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q)
            ((horizontalInsertionEquiv p q 0).symm ⟨s, h₀⟩)
            (X.δ 0 x) y) := by
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.simplex_horizontal_first_face X Y s h₀ x y, horizontalFirst_sign_int s h₀]

/-- 概要：水平終端の符号つき面は第一の入力の最後の面を用いる（Berger–Fresse §1.1.3）。
方針：終端の水平座標を最後の頂点と同定して水平面の符号公式を使う。
規約：第一の入力の最後の面の境界符号は (−1)^(p+1) である。
使われ方：Leibniz 則の第一の入力の最後の境界項を同定する。 -/
lemma shuffle_horizontal_last_face_signed (A : Type u) [CommRing A]
    (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (ha : a ∈ s.val) (hlast : a.val + 1 = p + 1 + q)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    (-1 : ℤ) ^ (a.val + 1) • (s.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
        ((X ⊗ Y).map (horizontalFaceMap p q a).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s x y)) =
      (-1 : ℤ) ^ (p + 1) •
        (((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).sign : ℤ) •
          _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q)
              ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩)
              (X.δ (Fin.last (p + 1)) x) y) := by
  have hend : a.succ = Fin.last (p + 1 + q) := Fin.ext hlast
  have hsign := horizontalBoundary_sign_int s a ha
  rw [hend, s.horizontal_endpoints.2] at hsign
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.simplex_horizontal_last_face X Y s a ha hlast x y]
  simp only [smul_smul]
  rw [hsign]
  simp only [Fin.val_last]

end SerrePositivity.SimplicialChains.Shuffle
