module
public import SerrePositivity.KST.SConstruction.SimplexHAFaceVertex
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetFilters

/-! # 元の面頂点の右側頂点数と HA 符号
概要：元の面座標 i に対応する内部頂点の右には、i 個の列頂点と右側集合がある。
方針：元の右端でのフィルターの一致と、辺保持による右側集合への移動で帰納する。
規約：元の右端座標・頂点順を保持。使われ方：HA 項と元の全面境界の符号比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の面頂点番号は、元の面座標を一意に決める。 -/
lemma simplexHAFaceVertex_injective (m : ℕ) : Function.Injective (simplexHAFaceVertex m) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  dsimp only [simplexHAFaceVertex] at h
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- 元の面頂点より右の頂点数は、元の面座標と右側頂点数の和。 -/
lemma simplexHAFaceVertex_right_count {n : ℕ} (m : ℕ)
    (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) (i : Fin (m + 1)) :
    ((simplexHADecodeSubset (m + 1) v T).filter (v (simplexHAFaceVertex m i) < ·)).card =
      i.val + T.card := by
  have hz (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
      (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
      ((simplexHADecodeSubset (m + 1) v T).filter
        (v (simplexHAFaceVertex m 0) < ·)).card = 0 + T.card := by
    rw [simplexHAFaceVertex_zero, simplexHADecodeSubset_filter_strict_right m v T hb, zero_add]
  induction m generalizing T with
  | zero =>
    have hi : i = 0 := Fin.ext (by have hi := i.isLt; omega)
    subst i
    exact hz 0 v T hb
  | succ m ih =>
    refine Fin.cases (hz (m + 1) v T hb) (fun j => ?_) i
    let r := v (Fin.last (m + 2))
    have he : (simplexHADecodeSubset (m + 1) (Fin.castSuccOrderEmb.trans v) (insert r T)).filter
        ((Fin.castSuccOrderEmb.trans v) (simplexHAFaceVertex m j) < ·) =
        (simplexHADecodeSubset (m + 2) v T).filter
          (v (simplexHAFaceVertex (m + 1) j.succ) < ·) := by
      rw [simplexHADecodeSubset_insert_tail, simplexHAFaceVertex_succ]
      rfl
    have hc := Finset.card_insert_of_notMem (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T r hb)
    rw [← he, ih (Fin.castSuccOrderEmb.trans v) (insert r T)
      (simplexHADecodePrefix_insert (m + 1) v T hb) j]
    change j.val + (insert r T).card = (j.val + 1) + T.card
    omega

/-- 元の右側集合が一点なら、HA 項の符号は元の面座標に一を足した指数。 -/
lemma simplexHAFaceVertex_sign {n : ℕ} (m : ℕ)
    (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    (((simplexHADecodeSubset (m + 1) v {b}).filter
      (v (simplexHAFaceVertex m i) < ·)).card : ℤ).negOnePow =
        ((i.val : ℤ) + 1).negOnePow := by
  have h := simplexHAFaceVertex_right_count m v {b}
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) i
  rw [h, Finset.card_singleton, Nat.cast_add, Nat.cast_one]

end SerrePositivity.KST.SConstruction
