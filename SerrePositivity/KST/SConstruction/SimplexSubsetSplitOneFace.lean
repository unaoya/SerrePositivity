module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitRefinementComparison

/-! # 元の部分集合分割の実標準一面
概要：元の左右フィルターを貼る実射の cube を、元の共有頂点の標準一面と同定する。
方針：既存の二 bead refinement の一面因子分解に、元の長さ移送を合成する。
規約：元の具体的 cube 射と全頂点を保持。使われ方：同じ Serre Hom への一面生成射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の二 bead の共有座標の標準一面と、元の逆次元移送の合成。 -/
def necklaceWedgeBeadRefinementFace (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single p).wedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single q)).dimension ⟶
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (p + q)).dimension :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single p).wedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single q)).dimension
    (Fin.cast (necklaceWedgeBead_codimension p q hp hq)
      (necklaceRefinementMissingCoordinate
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} p) (necklaceBead q))
        (necklaceWedgeBeadSeam p q hp hq))) ≫
    (concreteCubeDimensionIso
      (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (p + q)).dimension)
      (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk
        (((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single p).wedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single q)).dimension + 1))
      (necklaceWedgeBead_codimension p q hp hq)).inv

/-- 元の標準一面因子は、元の二 bead refinement cube 射そのもの。 -/
lemma necklaceWedgeBeadRefinementFace_eq (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    necklaceWedgeBeadRefinementFace.{u} p q hp hq =
      necklaceConcreteCubeMap (necklaceWedgeBeadRefinement.{u} p q) :=
  (necklaceRefinement_cube_factor
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} p) (necklaceBead q))
    (necklaceWedgeBeadSeam p q hp hq)
    (necklaceWedgeBead_joints p q)).symm

/-- 元の分割 refinement は、元の共有座標の標準一面と元の次元移送からなる。 -/
lemma simplexSubsetSplitRefinement_one_face {n : ℕ} (I : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    necklaceConcreteCubeMap (simplexSubsetSplitRefinement.{u} I j hj hL hR) =
      necklaceWedgeBeadRefinementFace.{u} ((I.filter (· ≤ j)).card - 1)
        ((I.filter (j ≤ ·)).card - 1) (by omega) (by omega) ≫
      (concreteCubeDimensionIso (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single k).dimension)
        (simplexSubsetSplit_length I j hj hL hR))).hom := by
  exact (simplexSubsetSplitRefinement_cube_eq I j hj hL hR).trans
    (congrArg (fun f => f ≫ (concreteCubeDimensionIso
      (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single k).dimension)
        (simplexSubsetSplit_length I j hj hL hR))).hom)
      (necklaceWedgeBeadRefinementFace_eq.{u} _ _ (by omega) (by omega)).symm)

end SerrePositivity.KST.SConstruction
