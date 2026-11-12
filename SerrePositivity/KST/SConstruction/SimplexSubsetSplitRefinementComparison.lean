module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitAugmentation

/-! # 元の分割射と二 bead refinement の一致
概要：元の左右部分集合から作った実射を、既存の全頂点保存 refinement と同定する。
方針：元の長さの等号移送と、全頂点による元の necklace 射の一意性を使う。
規約：元の全単体的射を比較。使われ方：元の標準一面を分割 augmentation へ移す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の bead の長さの等号移送は、元の全頂点の同じ番号を保つ。 -/
lemma necklaceBead_eqToHom_vertex {p q : ℕ} (h : p = q)
    (v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single p).Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (eqToHom (congrArg necklaceBead.{u} h)) v =
      Fin.cast (congrArg Nat.succ h) v := by
  cases h
  exact congrFun (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_id _) v

/-- 元の分割 refinement は、元の二 bead refinement と同じ長さ移送の合成。 -/
lemma simplexSubsetSplitRefinement_eq {n : ℕ} (I : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    simplexSubsetSplitRefinement.{u} I j hj hL hR =
      necklaceWedgeBeadRefinement ((I.filter (· ≤ j)).card - 1)
        ((I.filter (j ≤ ·)).card - 1) ≫
      eqToHom (congrArg necklaceBead (simplexSubsetSplit_length I j hj hL hR)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_injective
  funext v
  rw [simplexSubsetSplitRefinement_vertex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_comp]
  exact (necklaceBead_eqToHom_vertex (simplexSubsetSplit_length I j hj hL hR) v).symm

/-- 元の bead の長さ移送の cube は、同じ元の次元移送そのもの。 -/
lemma necklaceBead_eqToHom_cube {p q : ℕ} (h : p = q) :
    necklaceConcreteCubeMap (eqToHom (congrArg necklaceBead.{u} h)) =
      (concreteCubeDimensionIso
        (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single k).dimension) h)).hom := by
  cases h
  exact necklaceConcreteCube.map_id _

/-- 元の分割 refinement の cube は、元の二 bead refinement cube と次元移送の合成。 -/
lemma simplexSubsetSplitRefinement_cube_eq {n : ℕ} (I : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    necklaceConcreteCubeMap (simplexSubsetSplitRefinement.{u} I j hj hL hR) =
      necklaceConcreteCubeMap (necklaceWedgeBeadRefinement.{u}
        ((I.filter (· ≤ j)).card - 1) ((I.filter (j ≤ ·)).card - 1)) ≫
      (concreteCubeDimensionIso (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single k).dimension)
        (simplexSubsetSplit_length I j hj hL hR))).hom := by
  rw [simplexSubsetSplitRefinement_eq]
  exact (necklaceConcreteCube.map_comp _ _).trans
    (congrArg (fun g => necklaceConcreteCubeMap (necklaceWedgeBeadRefinement.{u}
      ((I.filter (· ≤ j)).card - 1) ((I.filter (j ≤ ·)).card - 1)) ≫ g)
      (necklaceBead_eqToHom_cube (simplexSubsetSplit_length I j hj hL hR)))

end SerrePositivity.KST.SConstruction
