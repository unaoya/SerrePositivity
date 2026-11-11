module
public import SerrePositivity.KST.SConstruction.NecklaceRefinementInSimplex
public import SerrePositivity.KST.SConstruction.NecklaceRefinementOneFace
public import SerrePositivity.KST.SConstruction.SimplexBeadLambdaHom

/-! # 元の標準一面と refinement の Serre 生成射
概要：元の標準一面と同じ一 bead の実生成射の合成は、元の三 joint necklace の生成射。
方針：元の実可換三角形を元の Serre 関手へ送り、元の一面の同定を合成する。
規約：元の Hom 複体と元の全単体的包含を保持。使われ方：分割合成項の実鎖射の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の標準単体内の全頂点包含が定める、元の Λ Hom への Serre 生成射。 -/
def necklaceRefinementLambdaCell (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    serreCubeComplex A T.down.dimension ⟶
      homObject A (CubicalLambda A (Δ[T.down.vertexMax] : SSet.{u}))
        (simplexBeadFirstVertex T.down.vertexMax) (simplexBeadLastVertex T.down.vertexMax) :=
  (cubicalSerreChainsCubeIso A).hom.app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.down.dimension) ≫
    (cubicalSerreChains A).map (necklaceCubicalCell (necklaceInStandardSimplex T))

/-- 元の refinement の Serre 射は、元の同じ標準単体内の生成射と厳密に可換。 -/
lemma necklaceRefinementLambdaCell_comparison (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    (serreConcreteCubeComplexFunctor A).map
        (necklaceConcreteCubeMap (necklaceBeadRefinement T)) ≫
      necklaceRefinementLambdaCell A (necklaceBead T.down.vertexMax) =
        necklaceRefinementLambdaCell A T := by
  have h := congrArg ((cubicalSerreChains A).map) (necklaceInBeadRefinement_cell T)
  have ht := (cubicalSerreChainsCubeIso A).hom.naturality
    (necklaceConcreteCubeMap (necklaceBeadRefinement T))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cubicalSerreChains A).map
      (necklaceCubicalCell (necklaceInStandardSimplex (necklaceBead T.down.vertexMax)))) ht).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => (cubicalSerreChainsCubeIso A).hom.app _ ≫ f)
          ((cubicalSerreChains A).map_comp _ _).symm).trans
            (congrArg (fun f => (cubicalSerreChainsCubeIso A).hom.app _ ≫ f) h))))

/-- 元の鎖一面と同じ実生成射の合成は、元の三 joint necklace の Serre 生成射を回収する。 -/
lemma necklaceRefinementLambdaCell_one_face (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u})
    (j : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).NonjointVertex)
    (hJ : T.down.joints = {0, j.val.val, T.down.vertexMax}) :
    (serreCubeFace A true T.down.dimension
        (Fin.cast (necklaceRefinementMissingCoordinate_codimension T j hJ)
          (necklaceRefinementMissingCoordinate T j))).hom ≫
      (serreConcreteCubeComplexFunctor A).map
        (concreteCubeDimensionIso
          (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).dimension)
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + 1))
          (necklaceRefinementMissingCoordinate_codimension T j hJ)).inv ≫
        necklaceRefinementLambdaCell A (necklaceBead T.down.vertexMax) =
      necklaceRefinementLambdaCell A T := by
  have hf := congrArg (fun f => f.hom) (serreConcreteCubeMap_face A true T.down.dimension
    (Fin.cast (necklaceRefinementMissingCoordinate_codimension T j hJ)
      (necklaceRefinementMissingCoordinate T j)))
  have h := congrArg ((serreConcreteCubeComplexFunctor A).map)
    (necklaceRefinement_cube_factor T j hJ)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ necklaceRefinementLambdaCell A (necklaceBead T.down.vertexMax))
      ((congrArg (fun f => f ≫ (serreConcreteCubeComplexFunctor A).map
        (concreteCubeDimensionIso
          (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).dimension)
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + 1))
          (necklaceRefinementMissingCoordinate_codimension T j hJ)).inv) hf.symm).trans
        (((serreConcreteCubeComplexFunctor A).map_comp _ _).symm.trans h.symm))).trans
          (necklaceRefinementLambdaCell_comparison A T))

end SerrePositivity.KST.SConstruction
