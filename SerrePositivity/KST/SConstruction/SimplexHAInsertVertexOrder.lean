module
public import SerrePositivity.KST.SConstruction.SimplexHADeleteVertexSubset
public import Mathlib.Data.Finset.Sort

/-! # 元の HA 頂点列への欠落頂点の昇順挿入
概要：元の列に属さない頂点を一つ加え、同じ全頂点像を持つ昇順列を作る。
方針：元の有限像への insert と元の orderEmbOfFin を使う。
規約：元の頂点番号と始点を保持。使われ方：全区間から任意部分集合への削除帰納。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の欠落頂点を加えた頂点像の濃度は、元の列の長さに一を加えた値。 -/
lemma simplexHAInsertVertexOrder_card {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) :
    (insert j (Finset.univ.map v.toEmbedding)).card = m + 2 := by
  rw [Finset.card_insert_of_notMem hj, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- 元の列に欠落頂点を一つ加えた、元の同じ番号の昇順列。 -/
def simplexHAInsertVertexOrder {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) :
    Fin (m + 2) ↪o Fin (N + 1) :=
  (insert j (Finset.univ.map v.toEmbedding)).orderEmbOfFin (simplexHAInsertVertexOrder_card v j hj)

/-- 元の挿入列の頂点像は、元の列の全頂点像に同じ欠落頂点を加えた集合。 -/
lemma simplexHAInsertVertexOrder_vertices {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) :
    Finset.univ.map (simplexHAInsertVertexOrder v j hj).toEmbedding =
      insert j (Finset.univ.map v.toEmbedding) := by
  rw [Finset.map_eq_image]
  exact Finset.image_orderEmbOfFin_univ _ (simplexHAInsertVertexOrder_card v j hj)

/-- 元の挿入列内での、元の同じ挿入頂点の番号。 -/
def simplexHAInsertVertexIndex {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) : Fin (m + 2) :=
  ((insert j (Finset.univ.map v.toEmbedding)).orderIsoOfFin
    (simplexHAInsertVertexOrder_card v j hj)).symm
    ⟨j, Finset.mem_insert_self _ _⟩

/-- 元の挿入番号で元の挿入列を評価すると、同じ元の頂点が戻る。 -/
lemma simplexHAInsertVertexIndex_recovery {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) :
    simplexHAInsertVertexOrder v j hj (simplexHAInsertVertexIndex v j hj) = j :=
  congrArg Subtype.val
    (((insert j (Finset.univ.map v.toEmbedding)).orderIsoOfFin
      (simplexHAInsertVertexOrder_card v j hj)).apply_symm_apply
      ⟨j, Finset.mem_insert_self _ _⟩)

/-- 元の始点より右に頂点を挿入しても、元の昇順列の始点を変えない。 -/
lemma simplexHAInsertVertexOrder_first {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) (hfirst : v 0 < j) :
    simplexHAInsertVertexOrder v j hj 0 = v 0 := by
  rw [show simplexHAInsertVertexOrder v j hj 0 =
    (insert j (Finset.univ.map v.toEmbedding)).min' (by simp) from
      Finset.orderEmbOfFin_zero (simplexHAInsertVertexOrder_card v j hj) (by omega)]
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩))
  · have h := Finset.min'_mem (insert j (Finset.univ.map v.toEmbedding)) (by simp)
    rcases Finset.mem_insert.mp h with he | h
    · exact hfirst.le.trans_eq he.symm
    · obtain ⟨k, _, hk⟩ := Finset.mem_map.mp h
      exact hk ▸ v.monotone (Fin.zero_le k)

/-- 元の始点より右の挿入頂点は、元の挿入列でも零より大きい番号を持つ。 -/
lemma simplexHAInsertVertexIndex_pos {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) (hfirst : v 0 < j) :
    0 < simplexHAInsertVertexIndex v j hj := by
  apply Fin.pos_iff_ne_zero.mpr
  intro h
  have he := simplexHAInsertVertexIndex_recovery v j hj
  rw [h, simplexHAInsertVertexOrder_first v j hj hfirst] at he
  exact (ne_of_lt hfirst) he

/-- 元の列と挿入頂点が同じ終点より左なら、元の挿入列全体も同じ終点より左。 -/
lemma simplexHAInsertVertexOrder_last_lt {N m : ℕ} (v : Fin (m + 1) ↪o Fin (N + 1))
    (j : Fin (N + 1)) (hj : j ∉ Finset.univ.map v.toEmbedding) (b : Fin (N + 1))
    (hb : v (Fin.last m) < b) (hjb : j < b) :
    simplexHAInsertVertexOrder v j hj (Fin.last (m + 1)) < b := by
  have h : simplexHAInsertVertexOrder v j hj (Fin.last (m + 1)) ∈
      insert j (Finset.univ.map v.toEmbedding) :=
    (insert j (Finset.univ.map v.toEmbedding)).orderEmbOfFin_mem
      (simplexHAInsertVertexOrder_card v j hj) _
  rcases Finset.mem_insert.mp h with he | h
  · exact he.trans_lt hjb
  · obtain ⟨k, _, hk⟩ := Finset.mem_map.mp h
    exact hk ▸ (v.monotone (Fin.le_last k)).trans_lt hb

end SerrePositivity.KST.SConstruction
