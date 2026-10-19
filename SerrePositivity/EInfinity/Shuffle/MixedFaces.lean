module

public import SerrePositivity.EInfinity.Shuffle.Values
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapFaces

/-!
# 一般 shuffle の混合角の相殺

概要：Berger–Fresse §1.1.3 の混合角を交換した二項の面を比較する。
方針：面写像の像で水平・垂直座標が一致し、shuffle の符号が反転することを使う。
規約：一般の単体集合で、指定した頂点を避ける任意の引き戻しを扱う。
使われ方：一般 shuffle の微分の混合角の有限和を相殺する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Shuffle

open CategoryTheory MonoidalCategory BarrattEccles
open scoped Simplicial

/-- 概要：混合角を交換してもその頂点を避ける面は同じ（BF §1.1.3）。
方針：二座標の合成の等式を関手性で引き戻す。
規約：f の像は二辺の間の頂点 b を避ける。
使われ方：相殺する二項の単体の一致。 -/
lemma simplex_map_swapSteps (X Y : SSet.{0}) {p q r : ℕ}
    (s : ShufflePath p q) (a b : Fin (p + q)) (hab : b.val = a.val + 1)
    (f : ⦋r⦌ ⟶ ⦋p + q⦌) (hf : ∀ j, (f.toOrderHom j).val ≠ b.val)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (X ⊗ Y).map f.op (simplex X Y (s.swapSteps a b) x y) =
      (X ⊗ Y).map f.op (simplex X Y s x y) := by
  have hh : f ≫ (s.swapSteps a b).horizontalMap = f ≫ s.horizontalMap := by
    ext j : 3
    exact s.horizontal_swapSteps a b hab _ (hf j)
  have hv : f ≫ (s.swapSteps a b).verticalMap = f ≫ s.verticalMap := by
    ext j : 3
    exact s.vertical_swapSteps a b hab _ (hf j)
  apply Prod.ext
  · change X.map f.op (X.map (s.swapSteps a b).horizontalMap.op x) =
      X.map f.op (X.map s.horizontalMap.op x)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hh]
  · change Y.map f.op (Y.map (s.swapSteps a b).verticalMap.op y) =
      Y.map f.op (Y.map s.verticalMap.op y)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hv]

/-- 概要：混合角を交換した符号付き正規化面は相殺する（BF §1.1.3）。
方針：引き戻し単体の一致と隣接交換の符号反転を使う。
規約：任意の可換係数環で成立する。
使われ方：固定点のない involution による境界和の消滅。 -/
lemma swap_face_cancel (A : Type u) [CommRing A] (X Y : SSet.{0})
    {p q r : ℕ} (s : ShufflePath p q) (a b : Fin (p + q))
    (hab : b.val = a.val + 1) (hcross : a ∈ s.val ↔ b ∉ s.val)
    (f : ⦋r⦌ ⟶ ⦋p + q⦌) (hf : ∀ j, (f.toOrderHom j).val ≠ b.val)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    ((s.swapSteps a b).sign : ℤ) • AlexanderWhitney.generator A (X ⊗ Y) r
        ((X ⊗ Y).map f.op (simplex X Y (s.swapSteps a b) x y)) +
      (s.sign : ℤ) • AlexanderWhitney.generator A (X ⊗ Y) r
        ((X ⊗ Y).map f.op (simplex X Y s x y)) = 0 := by
  rw [simplex_map_swapSteps X Y s a b hab f hf x y, s.sign_swapSteps a b hab hcross]
  simp

end SerrePositivity.EInfinity.Shuffle
