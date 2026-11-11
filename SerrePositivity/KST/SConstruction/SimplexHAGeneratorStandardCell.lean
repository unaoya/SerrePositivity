module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorDecodeFace
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorRightComposition
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetOneFace
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetCellRecursion

/-! # 元の全生成元標準面と読み替え部分集合の実生成射
概要：読み替え次元の元の標準面を、同じ部分集合の実生成射へ前合成する。
方針：基底・零面・一面・辺保持を、元の両面式と tensor 表示で回収する。
規約：元の全生成元と実鎖射を保持。使われ方：bead 語の実鎖射との全生成元帰納。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全生成元標準面を、同じ読み替え部分集合の実生成射へ前合成する。 -/
def simplexHAGeneratorStandardCell {k : ℕ} (m : ℕ) (i : SerreCubeGeneratorIndex m)
    (v : Fin (m + 1) ↪o Fin (k + 1)) (T : Finset (Fin (k + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    serreCubeComplex A (serreCubeGeneratorFreeDimension m i + T.card - 1) ⟶
      homObject A (CubicalLambda A (Δ[k] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (T.max' hT)) :=
  serreCubeGeneratorDecodeFace A m i T hT ≫ simplexHADecodeSubsetCell A m v T hT hb

/-- 元の左生成元が零次元なら、同じ右側 bead の実鎖射に戻る。 -/
lemma simplexHAGeneratorStandardCell_zero {k : ℕ} (i : SerreCubeGeneratorIndex 0)
    (v : Fin 1 ↪o Fin (k + 1)) (T : Finset (Fin (k + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last 0) < t) :
    HEq (simplexHAGeneratorStandardCell A 0 i v T hT hb)
      (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v 0) hb)) := by
  have h : simplexHAGeneratorStandardCell A 0 i v T hT hb =
      simplexHADecodeSubsetCell A 0 v T hT hb := by
    unfold simplexHAGeneratorStandardCell
    rw [serreCubeGeneratorDecodeFace_zero_left]
    exact Category.id_comp _
  exact (heq_of_eq h).trans (simplexHADecodeSubsetCell_zero A v T hT hb)

/-- 元の零端点追加の標準面像は、同じ最右頂点を削除した前段の実標準面像。 -/
lemma simplexHAGeneratorStandardCell_point_zero {k : ℕ} (m : ℕ)
    (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1 + 1) ↪o Fin (k + 1))
    (T : Finset (Fin (k + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    simplexHAGeneratorStandardCell A (m + 1) (i, 0) v T hT hb =
      simplexHAGeneratorStandardCell A m i (Fin.castSuccOrderEmb.trans v) T hT
        (simplexHADecodePrefix_tail m v T hb) := by
  have h := congrArg (fun f => f ≫ simplexHADecodeSubsetCell A (m + 1) v T hT hb)
    (serreCubeGeneratorDecodeFace_point_zero A m i T hT)
  exact h.trans ((Category.assoc _ _ _).trans
    (congrArg (fun g => serreCubeGeneratorDecodeFace A m i T hT ≫ g)
      (simplexHADecodeSubsetCell_zero_face A m v T hT hb)))

/-- 元の一端点追加の標準面像は、同じ前段の標準面像と右側 bead の実分割合成。 -/
lemma simplexHAGeneratorStandardCell_point_one {k : ℕ} (m : ℕ)
    (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1 + 1) ↪o Fin (k + 1))
    (T : Finset (Fin (k + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    HEq (simplexHAGeneratorStandardCell A (m + 1) (i, 1) v T hT hb)
      (serreCubeChainComposition A (serreCubeGeneratorFreeDimension m i) (T.card - 1)
        (simplexHAGeneratorStandardCell A m i (Fin.castSuccOrderEmb.trans v)
          {v (Fin.last (m + 1))} (Finset.singleton_nonempty _) (simplexHADecodePrefix_cut m v))
        (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb))) := by
  let r := v (Fin.last (m + 1))
  let left := simplexHADecodeSubsetCell A m (Fin.castSuccOrderEmb.trans v)
    {r} (Finset.singleton_nonempty r) (simplexHADecodePrefix_cut m v)
  let right := simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT r hb)
  let face := serreCubeChainFace A true (m + T.card - 1) ((m + 1) + T.card - 1)
    (simplexHADecodeSubset_face_codimension m T hT) (simplexHADecodeFaceCoordinate m T hT)
  have he : simplexHAGeneratorStandardCell A (m + 1) (i, 1) v T hT hb =
      serreCubeGeneratorDecodeFace A m i T hT ≫
        (face ≫ simplexHADecodeSubsetCell A (m + 1) v T hT hb) :=
    (congrArg (fun f => f ≫ simplexHADecodeSubsetCell A (m + 1) v T hT hb)
      (serreCubeGeneratorDecodeFace_point_one A m i T hT)).trans (Category.assoc _ _ _)
  have ht := serreCubeChain_comp_heq A
    (serreCubeTail_dimension (serreCubeGeneratorFreeDimension m i) T hT)
    (serreCubeTail_dimension m T hT) rfl
    (serreCubeGeneratorDecodeFace A m i T hT)
    (serreCubeGeneratorRightFace A m i (T.card - 1)).hom
    (face ≫ simplexHADecodeSubsetCell A (m + 1) v T hT hb)
    (serreCubeChainComposition A m (T.card - 1) left right)
    (serreCubeGeneratorDecodeFace_heq A m i T hT)
    (simplexHADecodeSubsetCell_one_face_heq A m v T hT hb)
  have hs := congrArg (fun f => f ≫ left) (serreCubeGeneratorDecodeFace_singleton A m i r)
  exact (heq_of_eq he).trans (ht.trans
    ((heq_of_eq (serreCubeGeneratorRightFace_composition A m i (T.card - 1) left right)).trans
      (heq_of_eq (congrArg (fun f =>
        serreCubeChainComposition A (serreCubeGeneratorFreeDimension m i) (T.card - 1) f right)
          hs.symm))))

/-- 元の辺追加の標準面像は、同じ新頂点を右側集合へ移した前段の実標準面像。 -/
lemma simplexHAGeneratorStandardCell_edge {k : ℕ} (m : ℕ)
    (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1 + 1) ↪o Fin (k + 1))
    (T : Finset (Fin (k + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    HEq (simplexHAGeneratorStandardCell A (m + 1) (i, 2) v T hT hb)
      (simplexHAGeneratorStandardCell A m i (Fin.castSuccOrderEmb.trans v)
        (insert (v (Fin.last (m + 1))) T) (Finset.insert_nonempty _ T)
        (simplexHADecodePrefix_insert m v T hb)) := by
  let r := v (Fin.last (m + 1))
  have hn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T r hb
  have hc := Finset.card_insert_of_notMem hn
  have hp : serreCubeGeneratorFreeDimension (m + 1) (i, 2) + T.card - 1 =
      serreCubeGeneratorFreeDimension m i + (insert r T).card - 1 := by
    simp only [serreCubeGeneratorFreeDimension]
    omega
  have hq : (m + 1) + T.card - 1 = m + (insert r T).card - 1 := by omega
  have hK : homObject A (CubicalLambda A (Δ[k] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (T.max' hT)) =
      homObject A (CubicalLambda A (Δ[k] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex ((Fin.castSuccOrderEmb.trans v) 0))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex ((insert r T).max' (Finset.insert_nonempty r T))) := by
    exact congrArg (fun b => homObject A (CubicalLambda A (Δ[k] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (v 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT r hb).symm
  exact serreCubeChain_comp_heq A hp hq hK
    (serreCubeGeneratorDecodeFace A (m + 1) (i, 2) T hT)
    (serreCubeGeneratorDecodeFace A m i (insert r T) (Finset.insert_nonempty r T))
    (simplexHADecodeSubsetCell A (m + 1) v T hT hb)
    (simplexHADecodeSubsetCell A m (Fin.castSuccOrderEmb.trans v) (insert r T)
      (Finset.insert_nonempty r T) (simplexHADecodePrefix_insert m v T hb))
    (serreCubeGeneratorDecodeFace_edge A m i T hT r hn)
    (simplexHADecodeSubsetCell_edge A m v T hT hb).symm

end SerrePositivity.KST.SConstruction
