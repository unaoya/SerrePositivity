module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitNormalizedCube
public import SerrePositivity.KST.SConstruction.SimplexSubsetCubicalCell

/-! # 元の濃度次元の分割 cube と実分割射
概要：元の濃度次元の分割 cube は、元の部分集合分割 refinement と同じ実射を回収。
方針：元の標準二 bead refinement の比較と、元の次元移送の可換三角形を使う。
規約：元の実 cube 射を保持。使われ方：標準一面の最高生成元像と native 合成項の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
variable {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
  (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
  (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))

/-- 元の濃度次元の分割 cube の、元の実分割 refinement への可換三角形。 -/
lemma simplexSubsetSplitNormalizedCube_comparison :
    simplexSubsetSplitNormalizedCube.{u} I hI j hj hjm hjM ≫
      (simplexSubsetCubeDimensionIso.{u} I hI).hom =
    (concreteCubeDimensionIso
      (simplexSubsetSplit_wedge_erase_dimension I hI j hj hjm hjM).symm).hom ≫
      necklaceConcreteCubeMap (simplexSubsetSplitRefinement.{u} I j hj
        (simplexSubsetSplitLeft_two I hI j hj hjm)
        (simplexSubsetSplitRight_two I hI j hj hjM)) := by
  have hL := simplexSubsetSplitLeft_two I hI j hj hjm
  have hR := simplexSubsetSplitRight_two I hI j hj hjM
  have ht := concreteCubeDimensionIso_inv_comp_hom
    (simplexSubsetSplit_whole_dimension I hI j hj hL hR).symm
    (necklaceInSimplexSubset_dimension.{u} I hI).symm
    (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single k).dimension)
      (simplexSubsetSplit_length I j hj hL hR))
  erw [simplexSubsetSplitRefinement_cube_eq]
  change (_ ≫ _ ≫ _) ≫ (concreteCubeDimensionIso
    (necklaceInSimplexSubset_dimension.{u} I hI).symm).hom = _
  erw [Category.assoc, Category.assoc, ht]
  rfl

end SerrePositivity.KST.SConstruction
