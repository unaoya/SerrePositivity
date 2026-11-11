module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetRecursion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms

/-! # 元の標準面座標と読み替え内部頂点
概要：右端からの面座標 i を、元の昇順列の内部頂点 m+1−i に対応させる。
方針：元の数値座標と列の狭義単調性で、所属と両端との厳密な順序を示す。
規約：元の全頂点番号を保持。使われ方：HA 削除成分と実標準零面像の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の右端からの面座標に対応する、元の昇順列の内部頂点番号。 -/
def simplexHAFaceVertex (m : ℕ) (i : Fin (m + 1)) : Fin (m + 2) :=
  ⟨m + 1 - i.val, by omega⟩

/-- 元の零面座標は、元の列の最後の頂点番号。 -/
lemma simplexHAFaceVertex_zero (m : ℕ) :
    simplexHAFaceVertex m 0 = Fin.last (m + 1) := by
  apply Fin.ext
  simp only [simplexHAFaceVertex, Fin.val_zero, Nat.sub_zero, Fin.val_last]

/-- 元の内側面座標の内部頂点は、一段小さい列の同じ頂点の castSucc。 -/
lemma simplexHAFaceVertex_succ (m : ℕ) (i : Fin (m + 1)) :
    simplexHAFaceVertex (m + 1) i.succ = (simplexHAFaceVertex m i).castSucc := by
  apply Fin.ext
  simp only [simplexHAFaceVertex, Fin.val_succ, Fin.val_castSucc]
  omega

/-- 元の面座標に対応する番号は、元の始点番号より厳密に大きい。 -/
lemma simplexHAFaceVertex_pos (m : ℕ) (i : Fin (m + 1)) :
    (0 : Fin (m + 2)) < simplexHAFaceVertex m i := by
  change 0 < m + 1 - i.val
  omega

/-- 元の面座標に対応する頂点は、元の全頂点部分集合に所属する。 -/
lemma simplexHAFaceVertex_mem {n : ℕ} (m : ℕ)
    (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (i : Fin (m + 1)) :
    v (simplexHAFaceVertex m i) ∈ simplexHADecodeSubset (m + 1) v T :=
  (simplexHADecodeSubset_mem (m + 1) v T _).mpr (Or.inl ⟨_, rfl⟩)

/-- 元の面頂点は、元の列の始点より厳密に右。 -/
lemma simplexHAFaceVertex_first_lt {n : ℕ} (m : ℕ)
    (v : Fin (m + 2) ↪o Fin (n + 1)) (i : Fin (m + 1)) :
    v 0 < v (simplexHAFaceVertex m i) := v.strictMono (simplexHAFaceVertex_pos m i)

/-- 元の面頂点は、元の右側集合の全頂点より厳密に左。 -/
lemma simplexHAFaceVertex_tail_lt {n : ℕ} (m : ℕ)
    (v : Fin (m + 2) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (i : Fin (m + 1))
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    ∀ t ∈ T, v (simplexHAFaceVertex m i) < t :=
  fun t ht => (v.monotone (Fin.le_last _)).trans_lt (hb t ht)

end SerrePositivity.KST.SConstruction
