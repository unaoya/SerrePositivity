module
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetImage
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaNecklaceCell
public import SerrePositivity.KST.SConstruction.NecklaceLambdaCellPostcomposition

/-! # 元の単射な像部分集合の実 Serre cell
概要：元の部分集合上単射な入力写像の Λ 作用は、元の像部分集合の実 cell を回収する。
方針：元の necklace 後合成と augmentation 等号に、同じ標準次元の Serre 比較を使う。
規約：元の全次数・両端・濃度移送を保持。使われ方：native HA 単射成分の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の部分集合上単射な入力の Λ 作用は、元の像部分集合 cell を異種等号で回収。 -/
lemma simplexSubsetLambdaCellAt_image_inj_heq {M N : ℕ}
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hi : Set.InjOn α (I : Set (Fin (M + 1)))) (hJ : 2 ≤ (I.image α).card)
    (haJ : α a = (I.image α).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ))
    (hbJ : α b = (I.image α).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ)) :
    HEq (simplexSubsetLambdaCellAt A I a b hI ha hb ≫
      (cubicalLambdaMap A (stdSimplex.map (SimplexCategory.Hom.mk α))).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
      (simplexSubsetLambdaCellAt A (I.image α) (α a) (α b) hJ haJ hbJ) := by
  let φ := stdSimplex.map (SimplexCategory.Hom.mk α)
  let T := necklaceInSimplexSubsetAt.{u} I a b hI ha hb
  let P := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose φ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)).obj T
  have he : (simplexSubsetLambdaCellAt A I a b hI ha hb ≫
      (cubicalLambdaMap A φ).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) =
      eqToHom (congrArg (serreCubeComplex A) (necklaceInSimplexSubset_dimension.{u} I hI).symm) ≫
        necklaceLambdaCell A P :=
    (congrArg (fun f => f ≫ (cubicalLambdaMap A φ).map
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
      (simplexSubsetLambdaCellAt_necklace A I a b hI ha hb)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun f => eqToHom (congrArg (serreCubeComplex A)
            (necklaceInSimplexSubset_dimension.{u} I hI).symm) ≫ f)
            (necklaceLambdaCell_post A φ T)))
  have hP := necklaceLambdaCell_heq_of_eq A
    (necklaceInSimplexSubsetAt_image_inj α I a b hI ha hb hi hJ haJ hbJ)
  have hJcell := (heq_of_eq
    (simplexSubsetLambdaCellAt_necklace A (I.image α) (α a) (α b) hJ haJ hbJ)).trans
      (eqToHom_comp_heq _ _)
  exact ((heq_of_eq he).trans (eqToHom_comp_heq _ _)).trans (hP.trans hJcell.symm)

end SerrePositivity.KST.SConstruction
