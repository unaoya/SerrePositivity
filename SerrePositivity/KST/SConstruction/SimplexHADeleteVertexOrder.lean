module
public import SerrePositivity.KST.SConstruction.SimplexHAFaceVertex
public import SerrePositivity.KST.SConstruction.SimplexHAOrderAppendLast

/-! # 元の任意の面座標に対応する昇順頂点列の削除
概要：元の右端面座標に対応する内部頂点を削除し、他の全頂点を保つ。
方針：元の Fin.succAbove の順序埋め込みと、右端座標の再帰を使う。
規約：始点と元の頂点順を保持。使われ方：任意座標の零面への HA 線形復元の制限。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の面座標に対応する内部頂点だけを削除した、元の昇順列。 -/
def simplexHADeleteVertexOrder {n : ℕ} (m : ℕ) (q : Fin (m + 1))
    (v : Fin (m + 2) ↪o Fin (n + 1)) : Fin (m + 1) ↪o Fin (n + 1) :=
  (Fin.succAboveOrderEmb (simplexHAFaceVertex m q)).trans v

/-- 元の右端零面は、同じ最右頂点を除いた元の前段列を回収する。 -/
lemma simplexHADeleteVertexOrder_zero {n : ℕ} (m : ℕ)
    (v : Fin (m + 2) ↪o Fin (n + 1)) :
    simplexHADeleteVertexOrder m 0 v = Fin.castSuccOrderEmb.trans v := by
  ext j
  exact congrArg Fin.val (congrArg v (by
    rw [simplexHAFaceVertex_zero]
    exact Fin.succAbove_last_apply j))

/-- 元の内側頂点の削除と、元の最右頂点を除く制限は同じ前段削除を与える。 -/
lemma simplexHADeleteVertexOrder_succ_prefix {n : ℕ} (m : ℕ) (q : Fin (m + 1))
    (v : Fin (m + 3) ↪o Fin (n + 1)) :
    Fin.castSuccOrderEmb.trans (simplexHADeleteVertexOrder (m + 1) q.succ v) =
      simplexHADeleteVertexOrder m q (Fin.castSuccOrderEmb.trans v) := by
  ext j
  change (v ((simplexHAFaceVertex (m + 1) q.succ).succAbove j.castSucc)).val = _
  rw [simplexHAFaceVertex_succ]
  exact congrArg Fin.val (congrArg v Fin.castSucc_succAbove_castSucc)

/-- 元の内側頂点を削除しても、元の同じ最右頂点を保つ。 -/
lemma simplexHADeleteVertexOrder_succ_last {n : ℕ} (m : ℕ) (q : Fin (m + 1))
    (v : Fin (m + 3) ↪o Fin (n + 1)) :
    simplexHADeleteVertexOrder (m + 1) q.succ v (Fin.last (m + 1)) =
      v (Fin.last (m + 2)) := by
  change v ((simplexHAFaceVertex (m + 1) q.succ).succAbove (Fin.last (m + 1))) = _
  rw [simplexHAFaceVertex_succ]
  exact congrArg v (Fin.succAbove_ne_last_last (Fin.castSucc_ne_last _))

/-- 元の任意の内部頂点を削除しても、元の同じ始点を保つ。 -/
lemma simplexHADeleteVertexOrder_first {n : ℕ} (m : ℕ) (q : Fin (m + 1))
    (v : Fin (m + 2) ↪o Fin (n + 1)) : simplexHADeleteVertexOrder m q v 0 = v 0 := by
  exact congrArg v (Fin.succAbove_of_castSucc_lt _ _ (simplexHAFaceVertex_pos m q))

/-- 元の削除後の列も、元の右側集合より厳密に左にある。 -/
lemma simplexHADeleteVertexOrder_bound {n : ℕ} (m : ℕ) (q : Fin (m + 1))
    (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hb : ∀ r ∈ T, v (Fin.last (m + 1)) < r) :
    ∀ r ∈ T, simplexHADeleteVertexOrder m q v (Fin.last m) < r :=
  fun r hr => (v.monotone (Fin.le_last _)).trans_lt (hb r hr)

end SerrePositivity.KST.SConstruction
