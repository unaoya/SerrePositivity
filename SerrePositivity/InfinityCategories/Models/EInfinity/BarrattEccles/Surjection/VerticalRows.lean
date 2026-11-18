module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationCompositionValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Rows

/-!
模型。文献の定義との比較は後で
# 固定した外側頂点での実際の合成行列

概要：Berger–Fresse §1.5.7 の垂直成分の各行を実際の置換部分合成で作る。
方針：内側の置換と選択長さの列を、逆置換の行表示と合成置換の行表示へ移す。
規約：内側の行順と選択長さは保持する。
使われ方：元の内側の抽出証跡を固定外側の合成表へ転送する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：内側置換と選択長さの列を元の抽出行列へ移す（BF §1.5.7）。
方針：各逆置換を一行表示にする。
規約：空の列も許す。
使われ方：内側の元の成功証跡の入力。 -/
def permutationRows {n : ℕ} (vs : List (Equiv.Perm (Fin n) × ℕ)) :
    List (List (Fin n) × ℕ) :=
  vs.map (fun p => (List.ofFn p.1.symm, p.2))

/-- 概要：固定外側置換で各内側置換を合成した実際の行列（BF §1.5.7）。
方針：既存の permutationComposition の逆置換行を選択長さと組にする。
規約：内側の順序と長さを変更しない。
使われ方：垂直成分の実際の合成 table の入力。 -/
def fixedOuterRows {m n : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (vs : List (Equiv.Perm (Fin n) × ℕ)) : List (List (Fin (m + n)) × ℕ) :=
  vs.map (fun p => (List.ofFn (permutationComposition m n k σ p.1).symm, p.2))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
