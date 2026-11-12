module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeValues
public import SerrePositivity.KST.SConstruction.SimplexHARawWordComposition

/-! # 元の生成元読み替えの生の HA 値の再帰式
概要：零端点・一端点・辺の読み替えを、元の向き補正前の生成元値で回収する。
方針：元の再添字付けと、生の連結値と豊穣順合成の同定を合成する。
規約：元の因子順と全次元の添字を保持。使われ方：逆 dg Hom 射の微分・合成保存。
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

/-- 元の零端点の生の HA 値は、同じ最右頂点を削除した元の生の値。 -/
lemma simplexHABeadWordDecode_zero_rawValue :
    simplexHABeadWordRawValue A s (simplexHABeadWordDecode (m + 1) (i, 0) v T hT hb) =
      simplexHABeadWordRawValue A s
        (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v) T hT
          (simplexHADecodePrefix_tail m v T hb)) :=
  congrArg (simplexHABeadWordRawValue A s) (simplexHABeadWordDecode_zero m i v T hT hb)

/-- 元の一端点の生の値は、元の左右の生の値の同じ因子順の豊穣合成。 -/
lemma simplexHABeadWordDecode_one_rawValue :
    HEq (simplexHABeadWordRawValue A s (simplexHABeadWordDecode (m + 1) (i, 1) v T hT hb))
      (forward A (n := -((serreCubeGeneratorFreeDimension m i + (T.card - 1) : ℕ) : ℤ))
        (simplexHABeadWordRawValue A s
          (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
            {v (Fin.last (m + 1))} (Finset.singleton_nonempty _)
            (simplexHADecodePrefix_cut m v)))
        (simplexHABeadWordRawValue A s
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb)) (by
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
  exact (simplexHABeadWordRawValue_reindex A s rfl he (left.join right)).trans
    (heq_of_eq (simplexHABeadWordRawValue_join A s left right))

/-- 元の辺の生の HA 値は、切断頂点を同じ右側集合に加えた元の読み替えの生の値。 -/
lemma simplexHABeadWordDecode_edge_rawValue :
    HEq (simplexHABeadWordRawValue A s (simplexHABeadWordDecode (m + 1) (i, 2) v T hT hb))
      (simplexHABeadWordRawValue A s
        (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
          (insert (v (Fin.last (m + 1))) T) (Finset.insert_nonempty _ T)
          (simplexHADecodePrefix_insert m v T hb))) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T (v (Fin.last (m + 1))) hb
  have hc := Finset.card_insert_of_notMem hn
  exact simplexHABeadWordRawValue_reindex A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT _ hb)
    (show serreCubeGeneratorFreeDimension m i + (insert (v (Fin.last (m + 1))) T).card - 1 =
      serreCubeGeneratorFreeDimension m i + 1 + T.card - 1 by omega) _

end SerrePositivity.KST.SConstruction
