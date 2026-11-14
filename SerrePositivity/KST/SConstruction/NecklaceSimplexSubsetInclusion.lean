module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexSubsetInclusionMap
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubset

/-! # 同じ元の両端を持つ部分集合 bead の実包含
概要：元の部分集合包含を、元の標準単体の上の全端点保存 necklace 射にする。
方針：元の単体的包含を元の一 bead の同型で移す。
規約：全高次単体と元の可換三角形を保持。使われ方：削除面の余極限表示関係。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
variable {n : ℕ} (I J : Finset (Fin (n + 1)))
  (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
  (hmin : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) = J.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))
  (hmax : I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) = J.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))

/-- 元の同じ両端を持つ部分集合の包含が定める、元の全単体的 necklace 射。 -/
def necklaceSimplexSubsetInclusion : necklaceBead.{u} (I.card - 1) ⟶
    necklaceBead (J.card - 1) where
  map := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap I J hI hJ hIJ ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv
  map_first := (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap.{u} I J hI hJ hIJ ≫
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv).app _) (simplexBeadFirstVertex_eq_standard _)).trans
      ((congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv.app _)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap_first I J hI hJ hIJ hmin)).trans (simplexBeadIso_inv_first _))
  map_last := (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap.{u} I J hI hJ hIJ ≫
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv).app _) (simplexBeadLastVertex_eq_standard _)).trans
      ((congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv.app _)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap_last I J hI hJ hIJ hmax)).trans (simplexBeadIso_inv_last _))

/-- 元の部分集合 bead の実包含は、元の標準単体への augmentation と厳密に可換。 -/
lemma necklaceSimplexSubsetInclusion_triangle :
    (necklaceSimplexSubsetInclusion.{u} I J hI hJ hIJ hmin hmax).map ≫
        (necklaceInSimplexSubset J hJ).map = (necklaceInSimplexSubset I hI).map := by
  change ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap I J hI hJ hIJ ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap J hJ) =
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap I hI
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun f => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫ f)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap_triangle I J hI hJ hIJ)

/-- 元の部分集合 bead の実包含の頂点作用は、同じ元の局所番号の包含。 -/
lemma necklaceSimplexSubsetInclusion_vertex (v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (I.card - 1)).Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (necklaceSimplexSubsetInclusion.{u} I J hI hJ hIJ hmin hmax) v =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder I J hI hJ hIJ v := rfl

/-- 元の部分集合 bead の実包含は、元の全頂点作用で単射。 -/
lemma necklaceSimplexSubsetInclusion_vertex_injective :
    Function.Injective
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (necklaceSimplexSubsetInclusion.{u} I J hI hJ hIJ hmin hmax)) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_injective I J hI hJ hIJ

end SerrePositivity.KST.SConstruction
