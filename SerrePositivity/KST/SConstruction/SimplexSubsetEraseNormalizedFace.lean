module
public import SerrePositivity.KST.SConstruction.SimplexSubsetEraseZeroFace
public import SerrePositivity.KST.SConstruction.SimplexSubsetCubicalInclusion

/-! # 濃度−2 次元の元の部分集合削除の標準零面
概要：HA 成分に使う元の数値次元を揃えた包含も、同じ欠落座標の標準零面。
方針：元の実 necklace の零面の同定を、元の次元同型による共役へ移す。
規約：元の cube 包含と生成射を保持。使われ方：HA 削除項の正規化した面の式。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
variable {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
  (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
  (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))

include hI hj hjm hjM in
/-- 元の所属内部点の削除は、元の濃度−2 次元でも余次元一。 -/
lemma simplexSubsetErase_normalized_codimension : I.card - 2 = (I.erase j).card - 2 + 1 := by
  have hE := simplexSubsetErase_two I hI j hjm hjM
  have hc := Finset.card_erase_add_one hj
  omega

/-- 元の削除頂点を、元の濃度−2 次元の同じ右端からの数値座標で読む。 -/
def simplexSubsetEraseNormalizedCoordinate : Fin (I.card - 2) :=
  Fin.cast (necklaceInSimplexSubset_dimension.{0} I hI)
    (simplexSubsetEraseCoordinate I hI j hj hjm hjM)

/-- 元の濃度−2 次元に揃えた削除の実 cube 包含も、元の同じ座標の標準零面。 -/
lemma simplexSubsetErase_normalized_zero_face :
    simplexSubsetCubeInclusion.{u} (I.erase j) I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (simplexSubsetErase_two I hI j hjm hjM) hI
        (Finset.erase_subset _ _) (simplexSubsetErase_min I hI j hjm hjM).symm
        (simplexSubsetErase_max I hI j hjm hjM).symm rfl rfl ≫
      (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
        (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((I.erase j).card - 2 + 1))
        (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)).hom =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace false ((I.erase j).card - 2)
      (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
        (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM)) :=
  concreteCube_zero_face_conjugate
    (necklaceInSimplexSubset_dimension.{u} (I.erase j)
      (simplexSubsetErase_two I hI j hjm hjM)).symm
    (necklaceInSimplexSubset_dimension.{u} I hI).symm
    (simplexSubsetEraseCoordinate_codimension I hI j hj hjm hjM)
    (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
    (necklaceConcreteCubeMap (necklaceInSimplexSubsetErase.{u} I hI j hjm hjM).necklaceHom)
    (simplexSubsetEraseCoordinate I hI j hj hjm hjM)
    (necklaceInSimplexSubsetErase_cube_zero_face.{u} I hI j hj hjm hjM)

end SerrePositivity.KST.SConstruction
