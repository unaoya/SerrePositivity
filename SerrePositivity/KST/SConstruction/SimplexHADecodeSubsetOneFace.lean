module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetZeroFace
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSplitChildren
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaSpecifiedOneDimension
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitDegrees

/-! # 元の読み替え次元の標準一面と左右の実鎖射
概要：元の一面で、前段の読み替え実生成射と同じ右側 bead の実 tensor 合成を回収。
方針：元の共通面座標・左右次元・端点と両生成射の異種等号を合成へ移す。
規約：元の実鎖射全体と tensor 順を保持。使われ方：全生成元語の一端点の帰納。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の読み替え次元の標準一面は、元の前段と右側 bead の実 Serre 分割合成。 -/
lemma simplexHADecodeSubsetCell_one_face_heq {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    HEq (serreCubeChainFace A true (m + T.card - 1) ((m + 1) + T.card - 1)
        (simplexHADecodeSubset_face_codimension m T hT) (simplexHADecodeFaceCoordinate m T hT) ≫
      simplexHADecodeSubsetCell A (m + 1) v T hT hb)
      (serreCubeChainComposition A m (T.card - 1)
        (simplexHADecodeSubsetCell A m (Fin.castSuccOrderEmb.trans v)
          {v (Fin.last (m + 1))} (Finset.singleton_nonempty _) (simplexHADecodePrefix_cut m v))
        (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb))) := by
  let I := simplexHADecodeSubset (m + 1) v T
  let r := v (Fin.last (m + 1))
  have hI : 2 ≤ I.card := simplexHADecodeSubset_two (m + 1) v T hT hb
  have hj : r ∈ I := simplexHADecodeSubset_cut_mem m v T
  have hmin := simplexHADecodeSubset_cut_min m v T hb
  have hmax := simplexHADecodeSubset_cut_max m v T hT hb
  have hp : m + T.card - 1 = (I.erase r).card - 2 := by
    dsimp only [I, r]
    rw [simplexHADecodeSubset_erase m v T hb,
      simplexHADecodeSubset_dimension m (Fin.castSuccOrderEmb.trans v) T
        (simplexHADecodePrefix_tail m v T hb)]
  have hq : (m + 1) + T.card - 1 = I.card - 2 :=
    (simplexHADecodeSubset_dimension (m + 1) v T hb).symm
  have hi : Fin.cast hq.symm (simplexSubsetEraseNormalizedCoordinate I hI r hj hmin hmax) =
      simplexHADecodeFaceCoordinate m T hT := by
    apply Fin.ext
    exact simplexHADecodeSubset_erase_coordinate m v T hT hb hI
  have hs := simplexSubsetLambdaCellAtDimension_one_face_heq A I hI r hj hmin hmax
    (v 0) (T.max' hT) (simplexHADecodeSubset_min (m + 1) v T hb).symm
    (simplexHADecodeSubset_max (m + 1) v T hT hb).symm
    (m + T.card - 1) ((m + 1) + T.card - 1) hp hq
    (simplexHADecodeSubset_face_codimension m T hT)
  rw [hi] at hs
  let L := necklaceInSimplexSubsetSplitLeft.{u} I hI r hj
    (simplexHADecodeSubset_left_two m v T hb)
  let R := necklaceInSimplexSubsetSplitRight.{u} I hI r hj
    (simplexHADecodeSubset_right_two m v T hT hb)
  have hL : L.necklace.down.dimension = m :=
    (necklaceInSimplexSubsetSplitLeft_dimension.{u} I hI r hj
      (simplexHADecodeSubset_left_two m v T hb)).trans
        (simplexHADecodeSubset_left_dimension m v T hb)
  have hR : R.necklace.down.dimension = T.card - 1 :=
    (necklaceInSimplexSubsetSplitRight_dimension.{u} I hI r hj
      (simplexHADecodeSubset_right_two m v T hT hb)).trans
        (simplexHADecodeSubset_right_dimension m v T hb)
  have ht := serreCubeChainComposition_heq A (D := CubicalLambda A (Δ[n] : SSet.{u}))
    (congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (simplexHADecodeSubset_min (m + 1) v T hb)) rfl
    (congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (simplexHADecodeSubset_max (m + 1) v T hT hb)) hL hR
    (necklaceLambdaCell A L) (necklaceLambdaCell A R)
    (simplexHADecodeSubsetCell A m (Fin.castSuccOrderEmb.trans v)
      {r} (Finset.singleton_nonempty r) (simplexHADecodePrefix_cut m v))
    (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT r hb))
    (simplexHADecodeSplitLeft_cell_heq A m v T hT hb)
    (simplexHADecodeSplitRight_cell_heq A m v T hT hb)
  exact hs.trans ht

/-- 元の読み替え次元の一面は、元の始域移送を明示すると同じ実分割合成と厳密に等しい。 -/
lemma simplexHADecodeSubsetCell_one_face {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    serreCubeChainFace A true (m + T.card - 1) ((m + 1) + T.card - 1)
        (simplexHADecodeSubset_face_codimension m T hT) (simplexHADecodeFaceCoordinate m T hT) ≫
      simplexHADecodeSubsetCell A (m + 1) v T hT hb =
    eqToHom (congrArg (serreCubeComplex A)
      (show m + T.card - 1 = m + (T.card - 1) by
        have hp := Finset.card_pos.mpr hT
        omega)) ≫
      serreCubeChainComposition A m (T.card - 1)
        (simplexHADecodeSubsetCell A m (Fin.castSuccOrderEmb.trans v)
          {v (Fin.last (m + 1))} (Finset.singleton_nonempty _) (simplexHADecodePrefix_cut m v))
        (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb)) :=
  serreCubeChain_eq_transport_of_heq A (by
    have hp := Finset.card_pos.mpr hT
    omega) _ _
    (simplexHADecodeSubsetCell_one_face_heq A m v T hT hb)

end SerrePositivity.KST.SConstruction
