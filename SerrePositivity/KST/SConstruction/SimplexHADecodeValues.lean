module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeEquations
public import SerrePositivity.KST.SConstruction.SimplexHAReindexEvaluation

/-! # 元の生成元読み替えの HA 値の再帰式
概要：零端点の削除、一端点の通常順合成、辺の内部頂点追加を実 HA 値で回収する。
方針：元の読み替えの再帰と、元の端点・自由次元移送の評価を合成する。
規約：全次元・全ての元の添字を保持。使われ方：逆 Hom 鎖射の微分可換性の帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
variable {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (m : ℕ) (i : SerreCubeGeneratorIndex m)
  (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
  (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t)

/-- 元の零端点の HA 値は、同じ最右頂点を削除した元の HA 値。 -/
lemma simplexHABeadWordDecode_zero_value :
    simplexHABeadWordValue A s (simplexHABeadWordDecode (m + 1) (i, 0) v T hT hb) =
      simplexHABeadWordValue A s
        (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v) T hT
          (simplexHADecodePrefix_tail m v T hb)) :=
  congrArg (simplexHABeadWordValue A s) (simplexHABeadWordDecode_zero m i v T hT hb)

/-- 元の一端点の HA 値は、元の切断頂点を共有する左右の値の通常順合成。 -/
lemma simplexHABeadWordDecode_one_value :
    HEq (simplexHABeadWordValue A s (simplexHABeadWordDecode (m + 1) (i, 1) v T hT hb))
      (compose A (n := -((serreCubeGeneratorFreeDimension m i + (T.card - 1) : ℕ) : ℤ))
        (simplexHABeadWordValue A s
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb))
        (simplexHABeadWordValue A s
          (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
            {v (Fin.last (m + 1))} (Finset.singleton_nonempty _)
            (simplexHADecodePrefix_cut m v))) (by
              simp only [Finset.card_singleton, Nat.add_sub_cancel, Nat.cast_add]
              omega)) := by
  let left : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n (v 0) (v (Fin.last (m + 1)))
      (serreCubeGeneratorFreeDimension m i) := by
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n ((Fin.castSuccOrderEmb.trans v) 0)
      (v (Fin.last (m + 1))) (serreCubeGeneratorFreeDimension m i)
    simpa only [Finset.card_singleton, Nat.add_sub_cancel, Finset.max'_singleton] using
      simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
        {v (Fin.last (m + 1))} (Finset.singleton_nonempty _) (simplexHADecodePrefix_cut m v)
  let right := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb
  have hp := Finset.card_pos.mpr hT
  have he : serreCubeGeneratorFreeDimension m i + (T.card - 1) =
      serreCubeGeneratorFreeDimension m i + T.card - 1 := by omega
  change HEq (simplexHABeadWordValue A s
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex rfl he (left.join right)))
      (simplexHABeadWordValue A s (left.join right))
  exact simplexHABeadWordValue_reindex A s rfl he (left.join right)

/-- 元の辺の HA 値は、切断頂点を同じ右側集合に加えた元の読み替えの値。 -/
lemma simplexHABeadWordDecode_edge_value :
    HEq (simplexHABeadWordValue A s (simplexHABeadWordDecode (m + 1) (i, 2) v T hT hb))
      (simplexHABeadWordValue A s
        (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
          (insert (v (Fin.last (m + 1))) T) (Finset.insert_nonempty _ T)
          (simplexHADecodePrefix_insert m v T hb))) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T (v (Fin.last (m + 1))) hb
  have hc := Finset.card_insert_of_notMem hn
  exact simplexHABeadWordValue_reindex A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT _ hb)
    (show serreCubeGeneratorFreeDimension m i + (insert (v (Fin.last (m + 1))) T).card - 1 =
      serreCubeGeneratorFreeDimension m i + 1 + T.card - 1 by omega) _

end SerrePositivity.KST.SConstruction
