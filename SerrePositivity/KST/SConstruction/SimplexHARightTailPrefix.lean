module
public import SerrePositivity.KST.SConstruction.SimplexHARightTailOrder
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorValues

/-! # 元の任意の右側集合の全辺付加による復元
概要：元の最大右端以外を列に戻し、全辺添字を付けた同じ語を回収する。
方針：最大元以外の昇順列と全辺付加の一般比較を適用する。
規約：元の始点・最大右端・自由次元を保持。使われ方：混在生成元の微分比較。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction

/-- 元の右側集合の最大元以外を元の前段列に追加した、有界な同じ頂点列。 -/
def simplexHARightTailPrefix {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1))
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty) (hb : ∀ r ∈ T, v (Fin.last m) < r) :
    {u : Fin (m + (T.erase (T.max' hT)).card + 1) ↪o Fin (n + 1) //
      u (Fin.last (m + (T.erase (T.max' hT)).card)) < T.max' hT} :=
  simplexHATailPrefix m v _ (simplexHARightTailOrder T hT)
    (simplexHARightTailOrder_separated m v T hT hb) (T.max' hT)
    (hb _ (Finset.max'_mem T hT)) (simplexHARightTailOrder_bound T hT)

/-- 元の任意の右側集合を列へ戻しても、元の同じ始点を保つ。 -/
lemma simplexHARightTailPrefix_first {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last m) < r) :
    (simplexHARightTailPrefix m v T hT hb).val 0 = v 0 :=
  simplexHATailPrefix_first m v _ _ _ _ _ _

/-- 元の全辺付加の自由次元は、元の右側集合を保つ語の同じ自由次元。 -/
lemma simplexHARightTailPrefix_dimension {n : ℕ} (m : ℕ)
    (i : SerreCubeGeneratorIndex m) (T : Finset (Fin (n + 1))) (hT : T.Nonempty) :
    serreCubeGeneratorFreeDimension (m + (T.erase (T.max' hT)).card)
      (serreCubeGeneratorRightIndex m i (T.erase (T.max' hT)).card) =
        serreCubeGeneratorFreeDimension m i + T.card - 1 := by
  rw [serreCubeGeneratorRightIndex_freeDimension, simplexHARightTailOrder_card]
  have hp := Finset.card_pos.mpr hT
  omega

/-- 元の全辺付加列の一点右端の読み替えは、元の任意の右側集合の語と一致する。 -/
lemma simplexHARightTailPrefix_decode {n : ℕ} (m : ℕ) (i : SerreCubeGeneratorIndex m)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last m) < r) :
    HEq (simplexHABeadWordDecode (m + (T.erase (T.max' hT)).card)
      (serreCubeGeneratorRightIndex m i (T.erase (T.max' hT)).card)
      (simplexHARightTailPrefix m v T hT hb).val {T.max' hT}
      (Finset.singleton_nonempty _) (fun _ hr =>
        (Finset.mem_singleton.mp hr) ▸ (simplexHARightTailPrefix m v T hT hb).property))
      (simplexHABeadWordDecode m i v T hT hb) := by
  have hmax : ∀ r ∈ ({T.max' hT} : Finset (Fin (n + 1))), T.max' hT ≤ r := by
    intro r hr
    exact le_of_eq (Finset.mem_singleton.mp hr).symm
  have h := simplexHABeadWordDecode_rightTail m i v _ (simplexHARightTailOrder T hT)
    (simplexHARightTailOrder_separated m v T hT hb) (T.max' hT)
    (hb _ (Finset.max'_mem T hT)) (simplexHARightTailOrder_bound T hT)
    {T.max' hT} (Finset.singleton_nonempty _) hmax
  exact h.trans (simplexHABeadWordDecode_congr_heq m i v v rfl _ T
    (simplexHARightTailOrder_range T hT)
    ((Finset.singleton_nonempty _).mono Finset.subset_union_right) hT
    (simplexHATailUnion_bound m v _ _ (simplexHARightTailOrder_separated m v T hT hb)
      _ (hb _ (Finset.max'_mem T hT)) _ hmax) hb)

/-- 元の全辺付加の生成元語は、元の任意の右側集合の読み替え語そのもの。 -/
lemma simplexHARightTailPrefix_word {n : ℕ} (m : ℕ) (i : SerreCubeGeneratorIndex m)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ r ∈ T, v (Fin.last m) < r) :
    HEq (simplexHAGeneratorWord (m + (T.erase (T.max' hT)).card)
      (serreCubeGeneratorRightIndex m i (T.erase (T.max' hT)).card)
      (simplexHARightTailPrefix m v T hT hb).val (T.max' hT)
      (simplexHARightTailPrefix m v T hT hb).property)
      (simplexHABeadWordDecode m i v T hT hb) :=
  simplexHARightTailPrefix_decode m i v T hT hb

end SerrePositivity.KST.SConstruction
