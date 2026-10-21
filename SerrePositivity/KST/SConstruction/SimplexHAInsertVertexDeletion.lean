module
public import SerrePositivity.KST.SConstruction.SimplexHAInsertVertexOrder
public import Mathlib.Order.Hom.Set

/-! # 元の挿入頂点の右端面座標と削除による回収
概要：元の列に加えた頂点に対応する面座標で削除すると、元の列を厳密に回収する。
方針：元の挿入番号を右端座標へ戻し、同じ有限像を持つ昇順列の一意性を使う。
規約：元の全頂点番号・始点を保持。使われ方：欠落頂点数による cell 回収の帰納。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の始点より右に挿入した頂点に対応する、元の右端からの面座標。 -/
def simplexHAInsertVertexCoordinate {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) (hfirst : v 0 < j) :
    Fin (m + 1) :=
  ⟨m + 1 - (simplexHAInsertVertexIndex v j hj).val, by
    have hp := simplexHAInsertVertexIndex_pos v j hj hfirst
    change 0 < (simplexHAInsertVertexIndex v j hj).val at hp
    omega⟩

/-- 元の挿入面座標に対応する頂点番号は、元の同じ挿入番号。 -/
lemma simplexHAInsertVertexCoordinate_vertex {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) (hfirst : v 0 < j) :
    simplexHAFaceVertex m (simplexHAInsertVertexCoordinate v j hj hfirst) =
      simplexHAInsertVertexIndex v j hj := by
  apply Fin.ext
  change m + 1 - (m + 1 - (simplexHAInsertVertexIndex v j hj).val) = _
  have hi := (simplexHAInsertVertexIndex v j hj).isLt
  omega

/-- 元の挿入面座標で元の挿入列を評価すると、同じ元の挿入頂点を回収する。 -/
lemma simplexHAInsertVertexOrder_faceVertex {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) (hfirst : v 0 < j) :
    simplexHAInsertVertexOrder v j hj
      (simplexHAFaceVertex m (simplexHAInsertVertexCoordinate v j hj hfirst)) = j := by
  rw [simplexHAInsertVertexCoordinate_vertex]
  exact simplexHAInsertVertexIndex_recovery v j hj

/-- 元の挿入頂点を同じ面座標で除くと、元の全昇順列が厳密に戻る。 -/
lemma simplexHAInsertVertexOrder_delete {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) (hfirst : v 0 < j) :
    simplexHADeleteVertexOrder m (simplexHAInsertVertexCoordinate v j hj hfirst)
      (simplexHAInsertVertexOrder v j hj) = v := by
  let w := simplexHAInsertVertexOrder v j hj
  let q := simplexHAInsertVertexCoordinate v j hj hfirst
  have hs := simplexHADeleteVertexOrder_subset m q w ∅ (fun _ ht => False.elim (by simp at ht))
  simp only [simplexHADecodeSubset, Finset.union_empty] at hs
  rw [simplexHAInsertVertexOrder_vertices, simplexHAInsertVertexOrder_faceVertex,
    Finset.erase_insert hj] at hs
  apply OrderEmbedding.eq_of_range_eq
  ext x
  have h := Finset.ext_iff.mp hs x
  simpa only [Set.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
    RelEmbedding.coe_toEmbedding] using h

end SerrePositivity.KST.SConstruction
