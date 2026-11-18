module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalRows

/-!
模型。文献の定義との比較は後で
# 固定した内側頂点での実際の合成行列

概要：Berger–Fresse §1.5.7 の水平成分の各行を実際の置換部分合成で作る。
方針：各外側置換と同じ内側置換を合成し、元の選択長さを保持する。
規約：元の外側頂点の順序を変更しない。
使われ方：元の外側の証跡を実際の水平合成ブロックへ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：各外側置換を固定した内側置換と合成した行列（BF §1.5.7）。
方針：既存の実際の置換部分合成を各元の頂点へ適用する。
規約：選択長さは元の外側の長さ。
使われ方：最終除外前の水平合成成分の table 入力。 -/
def fixedInnerRows {m n : ℕ} (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (vs : List (Equiv.Perm (Fin (m + 1)) × ℕ)) : List (List (Fin (m + n)) × ℕ) :=
  vs.map (fun p => (List.ofFn (_root_.SerrePositivity.EInfinity.BarrattEccles.permutationComposition m n k p.1 τ).symm, p.2))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
