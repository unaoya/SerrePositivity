module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeBounds

/-! # 元の零・一端点と辺の読み替えの三つの再帰式
概要：零端点は削除、一端点は左右連結、辺は右側頂点集合への追加を回収する。
方針：元の再帰を展開し、右端点・自由次元の等号による同じ語への移送を外す。
規約：零端点は等号、残る二つは異種等号。使われ方：実標準面との帰納的比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
variable {n : ℕ} (m : ℕ) (i : SerreCubeGeneratorIndex m)
  (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
  (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t)

/-- 元の零端点の読み替えは、元の最右頂点を削除した同じ読み替え。 -/
lemma simplexHABeadWordDecode_zero :
    simplexHABeadWordDecode (m + 1) (i, 0) v T hT hb =
      simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v) T hT
        (simplexHADecodePrefix_tail m v T hb) := by
  rfl

/-- 元の一端点の読み替えは、元の切断頂点を共有する同じ左右の語の連結。 -/
lemma simplexHABeadWordDecode_one :
    HEq (simplexHABeadWordDecode (m + 1) (i, 1) v T hT hb)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord.join
        (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
          {v (Fin.last (m + 1))} (Finset.singleton_nonempty _) (simplexHADecodePrefix_cut m v))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb)) := by
  have hp := Finset.card_pos.mpr hT
  let left : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n (v 0) (v (Fin.last (m + 1)))
      (serreCubeGeneratorFreeDimension m i) := by
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n ((Fin.castSuccOrderEmb.trans v) 0)
      (v (Fin.last (m + 1))) (serreCubeGeneratorFreeDimension m i)
    simpa only [Finset.card_singleton, Nat.add_sub_cancel, Finset.max'_singleton] using
      simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
        {v (Fin.last (m + 1))} (Finset.singleton_nonempty _) (simplexHADecodePrefix_cut m v)
  let right := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb
  have he : serreCubeGeneratorFreeDimension m i + (T.card - 1) =
      serreCubeGeneratorFreeDimension m i + T.card - 1 := by omega
  change HEq (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex rfl he (left.join right)) (left.join right)
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex_heq rfl he (left.join right)

/-- 元の辺の読み替えは、元の切断頂点を同じ右側集合へ加えた読み替え。 -/
lemma simplexHABeadWordDecode_edge :
    HEq (simplexHABeadWordDecode (m + 1) (i, 2) v T hT hb)
      (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
        (insert (v (Fin.last (m + 1))) T) (Finset.insert_nonempty _ T)
        (simplexHADecodePrefix_insert m v T hb)) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T (v (Fin.last (m + 1))) hb
  have hc := Finset.card_insert_of_notMem hn
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex_heq (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT _ hb)
    (show serreCubeGeneratorFreeDimension m i + (insert (v (Fin.last (m + 1))) T).card - 1 =
      serreCubeGeneratorFreeDimension m i + 1 + T.card - 1 by omega) _

end SerrePositivity.KST.SConstruction
