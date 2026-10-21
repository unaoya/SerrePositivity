module
public import SerrePositivity.KST.SConstruction.SimplexSubsetOrder
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubset

/-! # 元の部分集合の頂点の局所番号と内部座標
概要：元の所属頂点を昇順単体の局所番号で読み、厳密な内部頂点を元の非 joint 座標にする。
方針：元の昇順列挙の逆と、元の最小・最大端点の式を使う。
規約：元の頂点そのものを回収。使われ方：削除された内部点の零座標。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の部分集合に属する頂点の、元の同じ昇順列挙での局所番号。 -/
def simplexSubsetVertexIndex {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) : Fin (I.card - 1 + 1) :=
  (I.orderIsoOfFin (show I.card = I.card - 1 + 1 by omega)).symm ⟨j, hj⟩

/-- 元の所属頂点の局所番号は、元の昇順列挙で同じ頂点を回収する。 -/
lemma simplexSubsetVertexIndex_recovery {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) :
    simplexSubsetOrder I hI (simplexSubsetVertexIndex I hI j hj) = j :=
  congrArg Subtype.val
    ((I.orderIsoOfFin (show I.card = I.card - 1 + 1 by omega)).apply_symm_apply ⟨j, hj⟩)

/-- 元の局所番号の頂点を取り出して戻すと、元の同じ局所番号。 -/
lemma simplexSubsetVertexIndex_order {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (v : Fin (I.card - 1 + 1)) :
    simplexSubsetVertexIndex I hI (simplexSubsetOrder I hI v) (simplexSubsetOrder_mem I hI v) = v :=
  (I.orderIsoOfFin (show I.card = I.card - 1 + 1 by omega)).symm_apply_apply v

/-- 元の厳密な内部頂点は、同じ一 bead の元の非 joint 座標を与える。 -/
def simplexSubsetInteriorVertex {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I)
    (hmin : I.min' (Finset.card_pos.mp (by omega)) < j)
    (hmax : j < I.max' (Finset.card_pos.mp (by omega))) :
    (NecklaceShape.single (I.card - 1)).NonjointVertex :=
  ⟨simplexSubsetVertexIndex I hI j hj, by
    intro h
    simp only [NecklaceShape.single, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · have he : simplexSubsetVertexIndex I hI j hj = 0 := Fin.ext h
      have hf := (congrArg (simplexSubsetOrder I hI) he).trans (simplexSubsetOrder_first I hI)
      exact (ne_of_gt hmin) ((simplexSubsetVertexIndex_recovery I hI j hj).symm.trans hf)
    · have he : simplexSubsetVertexIndex I hI j hj = Fin.last (I.card - 1) := Fin.ext h
      have hf := (congrArg (simplexSubsetOrder I hI) he).trans (simplexSubsetOrder_last I hI)
      exact (ne_of_lt hmax) ((simplexSubsetVertexIndex_recovery I hI j hj).symm.trans hf)⟩

end SerrePositivity.KST.SConstruction
