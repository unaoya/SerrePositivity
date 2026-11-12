module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeValues

/-! # 元の生成元読み替えの実 Λ Hom 鎖射の再帰式
概要：零端点の削除、一端点の実 tensor 合成、辺の内部頂点追加を元の実鎖射で回収。
方針：元の読み替えと元の端点・自由次元移送の実鎖射の比較を使う。
規約：元の Serre tensor と dg 合成を保持。使われ方：元の標準面との帰納的同定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]
variable {n : ℕ} (m : ℕ) (i : SerreCubeGeneratorIndex m)
  (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
  (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t)

/-- 元の零端点の実鎖射は、元の最右頂点を削除した同じ読み替えの実鎖射。 -/
lemma simplexHABeadWordDecode_zero_cell :
    simplexHABeadWordCell A (simplexHABeadWordDecode (m + 1) (i, 0) v T hT hb) =
      simplexHABeadWordCell A
        (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v) T hT
          (simplexHADecodePrefix_tail m v T hb)) :=
  congrArg (simplexHABeadWordCell A) (simplexHABeadWordDecode_zero m i v T hT hb)

/-- 元の一端点の実鎖射は、元の切断頂点を共有する左右の実 tensor 合成。 -/
lemma simplexHABeadWordDecode_one_cell :
    HEq (simplexHABeadWordCell A (simplexHABeadWordDecode (m + 1) (i, 1) v T hT hb))
      ((serreCubeTensorIso A (serreCubeGeneratorFreeDimension m i) (T.card - 1)).hom.hom ≫
        (simplexHABeadWordCell A
          (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
            {v (Fin.last (m + 1))} (Finset.singleton_nonempty _)
            (simplexHADecodePrefix_cut m v)) ⊗ₘ
          simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb)) ≫
        eComp (C := CubicalLambda A (Δ[n] : SSet.{u})) (Complex A)
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v (Fin.last (m + 1))))
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (T.max' hT))) := by
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
  change HEq (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex rfl he (left.join right)))
    (simplexHABeadWordCell A (left.join right))
  exact simplexHABeadWordCell_reindex A rfl he (left.join right)

/-- 元の辺の実鎖射は、切断頂点を同じ右側集合に加えた元の読み替えの実鎖射。 -/
lemma simplexHABeadWordDecode_edge_cell :
    HEq (simplexHABeadWordCell A (simplexHABeadWordDecode (m + 1) (i, 2) v T hT hb))
      (simplexHABeadWordCell A
        (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
          (insert (v (Fin.last (m + 1))) T) (Finset.insert_nonempty _ T)
          (simplexHADecodePrefix_insert m v T hb))) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T (v (Fin.last (m + 1))) hb
  have hc := Finset.card_insert_of_notMem hn
  exact simplexHABeadWordCell_reindex A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT _ hb)
    (show serreCubeGeneratorFreeDimension m i + (insert (v (Fin.last (m + 1))) T).card - 1 =
      serreCubeGeneratorFreeDimension m i + 1 + T.card - 1 by omega) _

end SerrePositivity.KST.SConstruction
