module
public import SerrePositivity.KST.SConstruction.NecklaceWedgeNumericMap
public import SerrePositivity.KST.SConstruction.NecklaceConcreteCube
public import SerrePositivity.KST.SConstruction.ConcreteCubeDimensionIso
public import SerrePositivity.KST.SConstruction.ConcreteCubeTensor

/-! # 元の necklace の wedge と具体的 cube tensor の自然な比較
概要：元の全 necklace 射に自然な、同じ数値頂点作用を持つ tensor 同型を構成する。
方針：dimension 加法性による同型を、元の全連結頂点で照合する。
規約：右ブロックを先に数える元の tensor を保持。使われ方：Day 上の cubical 合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の左右の具体的 cube の tensor と、同じ wedge の cube との同型。 -/
def necklaceCubeTensorIso (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + U.down.dimension) ≅
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T U).down.dimension :=
  concreteCubeDimensionIso (T.down.wedge_dimension U.down).symm

/-- 元の tensor 同型は、元の全連結頂点を同じ necklace 頂点へ送る。 -/
lemma necklaceCubeTensorIso_hom_join (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u})
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.down.dimension) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex U.down.dimension) :
    (necklaceCubeTensorIso T U).hom.val (cubeVertexJoin x y) =
      (_root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeNumericJoin T.down) U.down x y := by
  exact (concreteCubeDimensionIso_hom_val
    (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + U.down.dimension))
    (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.wedge U.down).dimension)
    (T.down.wedge_dimension U.down).symm (cubeVertexJoin x y)).trans
      ((_root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeNumericJoin_cubeVertexJoin T.down) U.down x y).symm

/-- 元の全端点保存射で、同じ具体的 cube tensor の比較が厳密に可換。 -/
lemma necklaceCubeTensorIso_naturality {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}}
    (f : T ⟶ T') (g : U ⟶ U') :
    concreteCubeTensorMap (necklaceConcreteCubeMap f) (necklaceConcreteCubeMap g) ≫
        (necklaceCubeTensorIso T' U').hom =
      (necklaceCubeTensorIso T U).hom ≫ necklaceConcreteCubeMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g) := by
  apply Subtype.ext
  funext x
  obtain ⟨⟨a, b⟩, hx⟩ := (cubeVertexBlockEquiv T.down.dimension U.down.dimension).symm.surjective x
  change cubeVertexJoin a b = x at hx
  subst x
  change (necklaceCubeTensorIso T' U').hom.val
      (cubeVertexTensor (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap g) (cubeVertexJoin a b)) =
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g) ((necklaceCubeTensorIso T U).hom.val
      (cubeVertexJoin a b))
  rw [cubeVertexTensor_join, necklaceCubeTensorIso_hom_join, necklaceCubeTensorIso_hom_join,
    necklaceNumericMap_wedge_join]

/-- 元の全 necklace 射についての、具体的 cube の二変数 tensor 比較の自然同型。 -/
def necklaceCubeTensorNatIso :
    necklaceConcreteCube.{u}.prod necklaceConcreteCube.{u} ⋙ concreteCubeTensor ≅
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeFunctor ⋙ necklaceConcreteCube :=
  NatIso.ofComponents (fun p => necklaceCubeTensorIso p.1 p.2)
    (fun f => necklaceCubeTensorIso_naturality f.1 f.2)

end SerrePositivity.KST.SConstruction
