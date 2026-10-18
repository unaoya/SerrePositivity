module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapCoordinates
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleComponent

/-!
# 交換した shuffle 経路の面の相殺

概要：Berger–Fresse §1.1.3 の微分の計算で、混合角を交換した二つの項の相殺を証明する。
方針：中間頂点を避ける引き戻しでは二つの合成単体が等しく、shuffle 符号だけが反転する。
規約：中間頂点を避ける任意の単体圏の射について述べる。
使われ方：shuffle の Leibniz 則の混合角の寄与を消去する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：単体構造射による引き戻しは置換列の頂点の引き戻しである（Berger–Fresse §1.1.2）。
方針：codiscrete nerve の構造射を対象で評価する。
規約：f は [r] → [t] の単調写像である。
使われ方：shuffle 経路の面を頂点ごとに比較する。 -/
@[simp] lemma simplexEquiv_map (n r t : ℕ) (f : ⦋r⦌ ⟶ ⦋t⦌)
    (x : (simplicial n) _⦋t⦌) (j : Fin (r + 1)) :
    simplexEquiv n r ((simplicial n).map f.op x) j =
      simplexEquiv n t x (f.toOrderHom j) := rfl

/-- 概要：中間頂点を除けば交換した二つの shuffle 単体は一致する（Berger–Fresse §1.1.3）。
方針：引き戻しの各頂点で水平・垂直座標が交換前後で一致することを使う。
規約：f の像が交換される二辺の間の頂点を避けると仮定する。
使われ方：混合角を削除した境界面の一致を与える。 -/
lemma shuffleSimplex_map_swapSteps (m n : ℕ) (i : Fin (m + 1)) {p q r : ℕ}
    (s : ShufflePath p q) (a b : Fin (p + q)) (hab : b.val = a.val + 1)
    (f : ⦋r⦌ ⟶ ⦋p + q⦌) (hf : ∀ j, (f.toOrderHom j).val ≠ b.val)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    (simplicial (m + n)).map f.op (shuffleSimplex m n i (s.swapSteps a b) x y) =
      (simplicial (m + n)).map f.op (shuffleSimplex m n i s x y) := by
  apply (simplexEquiv (m + n) r).injective
  funext j
  simp only [simplexEquiv_map, simplexEquiv_shuffleSimplex]
  rw [s.horizontal_swapSteps a b hab _ (hf j), s.vertical_swapSteps a b hab _ (hf j)]

/-- 概要：混合角の二つの shuffle 項の符号つき面は相殺する（Berger–Fresse §1.1.3）。
方針：中間頂点を避ける面の一致と隣接交換の符号反転を組み合わせる。
規約：正規化鎖の任意の引き戻し次数 r で成立する。
使われ方：shuffle の微分の内部の混合角の和を involution で消去する。 -/
lemma shuffle_swap_face_cancel (A : Type u) [CommRing A] (m n : ℕ) (i : Fin (m + 1))
    {p q r : ℕ} (s : ShufflePath p q) (a b : Fin (p + q))
    (hab : b.val = a.val + 1) (hcross : a ∈ s.val ↔ b ∉ s.val)
    (f : ⦋r⦌ ⟶ ⦋p + q⦌) (hf : ∀ j, (f.toOrderHom j).val ≠ b.val)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    ((s.swapSteps a b).sign : ℤ) • normalizedGenerator A (m + n) r
        ((simplicial (m + n)).map f.op (shuffleSimplex m n i (s.swapSteps a b) x y)) +
      (s.sign : ℤ) • normalizedGenerator A (m + n) r
        ((simplicial (m + n)).map f.op (shuffleSimplex m n i s x y)) = 0 := by
  rw [shuffleSimplex_map_swapSteps m n i s a b hab f hf x y, s.sign_swapSteps a b hab hcross]
  simp

end SerrePositivity.EInfinity.BarrattEccles
