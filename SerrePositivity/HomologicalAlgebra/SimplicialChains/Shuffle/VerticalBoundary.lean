module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.EndpointFaces
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.Values
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalBoundary

/-!
# 一般 shuffle の垂直境界の符号

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

/-- 概要：連続する垂直辺の間の符号つき面は第二の入力の符号つき面に等しい（Berger–Fresse §1.1.3）。
方針：単体の面の一致を使った後、整数の符号比較をスカラーの積へ適用する。
規約：第二の入力の微分には (−1)^p が付く。
使われ方：Leibniz 則の内部の垂直面の各項を同定する。 -/
lemma shuffle_vertical_face_signed (A : Type u) [CommRing A]
    (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p (q + 1))
    (a b : Fin (p + (q + 1))) (hab : b.val = a.val + 1)
    (ha : a ∉ s.val) (hb : b ∉ s.val)
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    (-1 : ℤ) ^ (a.val + 1) • (s.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
        ((X ⊗ Y).δ a.succ
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) s x y)) =
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ (s.vertical a.succ).val •
        (((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).sign : ℤ) •
          _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q)
              ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩) x
              (Y.δ (s.vertical a.succ) y)) := by
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.simplex_vertical_face X Y s a b hab ha hb x y]
  simp only [smul_smul]
  rw [verticalBoundary_sign_int s a ha]
  rw [mul_assoc]

/-- 概要：垂直始端の符号つき面は第二の入力の最初の面を用いる（Berger–Fresse §1.1.3）。
方針：始端の単体の等式と垂直始端の符号公式を使う。
規約：最初の面の境界符号は 1 である。
使われ方：Leibniz 則の第二の入力の最初の境界項を同定する。 -/
lemma shuffle_vertical_first_face_signed (A : Type u) [CommRing A]
    (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p (q + 1))
    (h₀ : 0 ∉ s.val)
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    (s.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
        ((X ⊗ Y).δ 0
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) s x y)) =
      (-1 : ℤ) ^ p • (((verticalInsertionEquiv p q 0).symm ⟨s, h₀⟩).sign : ℤ) •
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q)
            ((verticalInsertionEquiv p q 0).symm ⟨s, h₀⟩) x (Y.δ 0 y)) := by
  erw [_root_.SerrePositivity.SimplicialChains.Shuffle.simplex_vertical_first_face X Y s h₀ x y,
    verticalFirst_sign_int s h₀, smul_smul]

/-- 概要：垂直終端の符号つき面は第二の入力の最後の面を用いる（Berger–Fresse §1.1.3）。
方針：終端の座標を最後の頂点と同定して垂直面の符号公式を使う。
規約：第二の入力の最後の面の境界符号は (−1)^(q+1) である。
使われ方：Leibniz 則の第二の入力の最後の境界項を同定する。 -/
lemma shuffle_vertical_last_face_signed (A : Type u) [CommRing A]
    (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p (q + 1))
    (a : Fin (p + (q + 1))) (ha : a ∉ s.val) (hlast : a.val + 1 = p + (q + 1))
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    (-1 : ℤ) ^ (a.val + 1) • (s.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
        ((X ⊗ Y).δ a.succ
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) s x y)) =
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ (q + 1) •
        (((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).sign : ℤ) •
          _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q)
              ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩) x
              (Y.δ (Fin.last (q + 1)) y)) := by
  have hend : a.succ = Fin.last (p + (q + 1)) := Fin.ext hlast
  have hsign := verticalBoundary_sign_int s a ha
  rw [hend, s.vertical_endpoints.2] at hsign
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.simplex_vertical_last_face X Y s a ha hlast x y]
  simp only [smul_smul]
  rw [hsign, mul_assoc]
  simp only [Fin.val_last]

end SerrePositivity.SimplicialChains.Shuffle
