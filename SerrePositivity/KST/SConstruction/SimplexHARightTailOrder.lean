module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeRightTail

/-! # 元の右側頂点集合の最後を除く昇順列
概要：非空な元の右側集合を、最後の頂点とそれより左の同じ頂点列に分ける。
方針：最大元を除いた集合の順序埋め込みと、元の有限集合の最大性を使う。
規約：元の頂点集合を保持。使われ方：任意の右側集合の全辺付加による復元。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction

/-- 元の右側集合の最大元以外を、同じ昇順で列挙する。 -/
def simplexHARightTailOrder {n : ℕ} (T : Finset (Fin (n + 1))) (hT : T.Nonempty) :
    Fin (T.erase (T.max' hT)).card ↪o Fin (n + 1) :=
  (T.erase (T.max' hT)).orderEmbOfFin rfl

/-- 元の昇順列の像と最後の一点は、元の右側集合そのもの。 -/
lemma simplexHARightTailOrder_range {n : ℕ} (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) :
    Finset.univ.map (simplexHARightTailOrder T hT).toEmbedding ∪ {T.max' hT} = T := by
  rw [simplexHARightTailOrder, Finset.map_orderEmbOfFin_univ]
  rw [Finset.union_singleton, Finset.insert_erase (Finset.max'_mem T hT)]

/-- 元の最大元を除いた列は、元の前段列の最後より全て右にある。 -/
lemma simplexHARightTailOrder_separated {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last m) < r) :
    ∀ j, v (Fin.last m) < simplexHARightTailOrder T hT j := by
  intro j
  exact hb _ (Finset.mem_of_mem_erase (Finset.orderEmbOfFin_mem _ rfl j))

/-- 元の最大元以外の昇順列は、元の同じ最大元より厳密に左にある。 -/
lemma simplexHARightTailOrder_bound {n : ℕ} (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) : ∀ j, simplexHARightTailOrder T hT j < T.max' hT := by
  intro j
  have hj := Finset.mem_erase.mp (Finset.orderEmbOfFin_mem (T.erase (T.max' hT)) rfl j)
  exact lt_of_le_of_ne (Finset.le_max' T _ hj.2) hj.1

/-- 元の右側集合の最大元以外の列の長さは、元の濃度より一つ少ない。 -/
lemma simplexHARightTailOrder_card {n : ℕ} (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) : (T.erase (T.max' hT)).card = T.card - 1 :=
  Finset.card_erase_of_mem (Finset.max'_mem T hT)

end SerrePositivity.KST.SConstruction
