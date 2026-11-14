module
public import SerrePositivity.KST.SConstruction.SimplexSubsetImageFactorMap
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetAt
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklacePostcomposition

/-! # 元の任意の単調写像の像部分集合 necklace 因子
概要：元の部分集合 augmentation の後合成を、元の像部分集合 bead を通して分解する。
方針：元の単体的番号因子を一 bead の同型で移し、全高次単体の可換三角形を使う。
規約：像が二点以上の分岐、元の全端点保存射を保持。使われ方：高次退化の実零性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の任意の単調写像が定める、元の像部分集合 bead への実 necklace 射。 -/
def necklaceSimplexSubsetImageFactor {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    necklaceBead.{u} (I.card - 1) ⟶ necklaceBead ((I.image α).card - 1) where
  map := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫
    simplexSubsetImageFactorMap α I hI hJ ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv
  map_first := (congrArg ((simplexSubsetImageFactorMap.{u} α I hI hJ ≫
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv).app _) (simplexBeadFirstVertex_eq_standard _)).trans
      ((congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv.app _)
        (simplexSubsetImageFactorMap_first α I hI hJ)).trans (simplexBeadIso_inv_first _))
  map_last := (congrArg ((simplexSubsetImageFactorMap.{u} α I hI hJ ≫
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv).app _) (simplexBeadLastVertex_eq_standard _)).trans
      ((congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv.app _)
        (simplexSubsetImageFactorMap_last α I hI hJ)).trans (simplexBeadIso_inv_last _))

/-- 元の像 necklace 因子は、元の部分集合 augmentation の後合成を厳密に回収する。 -/
lemma necklaceSimplexSubsetImageFactor_triangle {M N : ℕ}
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    (necklaceSimplexSubsetImageFactor.{u} α I hI hJ).map ≫
        (necklaceInSimplexSubset (I.image α) hJ).map =
      (necklaceInSimplexSubset I hI).map ≫
        SSet.stdSimplex.map (SimplexCategory.Hom.mk α) := by
  change ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫
    simplexSubsetImageFactorMap α I hI hJ ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap (I.image α) hJ) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun f => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫ f)
    (simplexSubsetImageFactorMap_triangle α I hI hJ)

/-- 元の指定端点を持つ像因子は、後合成と像部分集合の元の実可換三角形。 -/
def necklaceInSimplexSubsetImageFactor {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (a b : Fin (M + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hJ : 2 ≤ (I.image α).card)
    (haJ : α a = (I.image α).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ))
    (hbJ : α b = (I.image α).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex.{u} a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)).obj
        (necklaceInSimplexSubsetAt I a b hI ha hb) ⟶
      necklaceInSimplexSubsetAt (I.image α) (α a) (α b) hJ haJ hbJ where
  necklaceHom := necklaceSimplexSubsetImageFactor α I hI hJ
  w := necklaceSimplexSubsetImageFactor_triangle α I hI hJ

end SerrePositivity.KST.SConstruction
