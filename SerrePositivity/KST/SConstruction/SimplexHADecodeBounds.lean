module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordDecode

/-! # 元の生成元読み替えの左部分と右側頂点の順序
概要：最右座標を除いた元の昇順頂点列は、同じ切断頂点と未処理の右側頂点より左。
方針：元の順序埋め込みの狭義単調性と元の右側境界を合成する。
規約：元の頂点番号を保持。使われ方：読み替えの三つの再帰式の境界証明。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の最右座標を除いた列の最後は、元の切断頂点より厳密に左。 -/
lemma simplexHADecodePrefix_last {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) :
    (Fin.castSuccOrderEmb.trans v) (Fin.last m) < v (Fin.last (m + 1)) :=
  v.strictMono (Fin.castSucc_lt_last _)

/-- 元の左部分の最後は、元の全ての未処理の右側頂点より厳密に左。 -/
lemma simplexHADecodePrefix_tail {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    ∀ t ∈ T, (Fin.castSuccOrderEmb.trans v) (Fin.last m) < t :=
  fun t ht => (simplexHADecodePrefix_last m v).trans (hb t ht)

/-- 元の左部分の読み替えの右端を、元の切断頂点一点に指定できる。 -/
lemma simplexHADecodePrefix_cut {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) :
    ∀ t ∈ ({v (Fin.last (m + 1))} : Finset (Fin (n + 1))),
      (Fin.castSuccOrderEmb.trans v) (Fin.last m) < t := by
  intro t ht
  simpa only [Finset.mem_singleton.mp ht] using simplexHADecodePrefix_last m v

/-- 元の切断頂点を同じ未処理集合へ加えても、左部分の右側境界を保つ。 -/
lemma simplexHADecodePrefix_insert {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    ∀ t ∈ insert (v (Fin.last (m + 1))) T,
      (Fin.castSuccOrderEmb.trans v) (Fin.last m) < t := by
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact simplexHADecodePrefix_last m v
  · exact simplexHADecodePrefix_tail m v T hb t ht

end SerrePositivity.KST.SConstruction
