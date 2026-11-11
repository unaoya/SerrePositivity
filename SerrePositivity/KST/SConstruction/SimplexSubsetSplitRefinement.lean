module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitMap

/-! # 元の分割二 bead から全体の一 bead への実射
概要：元の左右部分集合の連結を、同じ全頂点の一 bead へ端点を保って送る。
方針：元の分割単体的射と一 bead の逆同型を合成する。
規約：全高次単体を保持。使われ方：元の augmentation の表示関係と標準一面の比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の分割射は、元の始零単体を同じ零番頂点に送る。 -/
lemma simplexSubsetSplitMap_first {n : ℕ} (I : Finset (Fin (n + 1))) (j : Fin (n + 1))
    (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (simplexSubsetSplitMap.{u} I j hj hL hR).app _
        (((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (· ≤ j)).card - 1)).wedge
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (j ≤ ·)).card - 1))).firstVertex) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0 := by
  apply SSet.stdSimplex.ext
  intro i
  exact Fin.ext rfl

/-- 元の分割射は、元の終零単体を同じ全体の最後の頂点に送る。 -/
lemma simplexSubsetSplitMap_last {n : ℕ} (I : Finset (Fin (n + 1))) (j : Fin (n + 1))
    (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (simplexSubsetSplitMap.{u} I j hj hL hR).app _
        (((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (· ≤ j)).card - 1)).wedge
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (j ≤ ·)).card - 1))).lastVertex) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (Fin.last (I.card - 1)) := by
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  exact simplexSubsetSplit_length I j hj hL hR

/-- 元の左右部分集合の二 bead から、同じ全体の一 bead への端点保存射。 -/
def simplexSubsetSplitRefinement {n : ℕ} (I : Finset (Fin (n + 1))) (j : Fin (n + 1))
    (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} ((I.filter (· ≤ j)).card - 1))
      (necklaceBead ((I.filter (j ≤ ·)).card - 1)) ⟶ necklaceBead (I.card - 1) where
  map := simplexSubsetSplitMap I j hj hL hR ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv
  map_first := (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv.app _)
    (simplexSubsetSplitMap_first I j hj hL hR)).trans (simplexBeadIso_inv_first _)
  map_last := (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv.app _)
    (simplexSubsetSplitMap_last I j hj hL hR)).trans (simplexBeadIso_inv_last _)

/-- 元の分割 refinement の全頂点番号は、元の同じ番号の等号移送。 -/
lemma simplexSubsetSplitRefinement_vertex {n : ℕ} (I : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card)
    (v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} ((I.filter (· ≤ j)).card - 1))
      (necklaceBead ((I.filter (j ≤ ·)).card - 1))).down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (simplexSubsetSplitRefinement I j hj hL hR) v =
      simplexSubsetSplitOrder I j hj hL hR v := rfl

/-- 元の分割 refinement は、同じ全体の単体への元の射を回収する。 -/
lemma simplexSubsetSplitRefinement_triangle {n : ℕ} (I : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (simplexSubsetSplitRefinement.{u} I j hj hL hR).map ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom = simplexSubsetSplitMap I j hj hL hR := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => simplexSubsetSplitMap I j hj hL hR ≫ f)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv_hom_id).trans (Category.comp_id _))

end SerrePositivity.KST.SConstruction
