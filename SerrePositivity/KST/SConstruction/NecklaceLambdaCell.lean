module
public import SerrePositivity.KST.SConstruction.CubicalLambdaComonoids

/-! # 元の全 necklace の Serre 生成射
概要：元の固定端点 necklace の生成射を、同じ Λ Hom の実鎖射に送る。
方針：元の Serre cube 比較と cubical 生成射を合成し、表示関係に自然性を使う。
規約：元の necklace の次元を保持。使われ方：部分集合分割の同じ実鎖射の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全 necklace の cubical 生成射を、同じ元の Λ Hom へ送る実 Serre 鎖射。 -/
def necklaceLambdaCell {K : SSet.{u}} {x y : K _⦋0⦌} (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    serreCubeComplex A T.necklace.down.dimension ⟶ homObject A (CubicalLambda A K) x y :=
  (cubicalSerreChainsCubeIso A).hom.app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.necklace.down.dimension) ≫
    (cubicalSerreChains A).map (necklaceCubicalCell T)

/-- 元の全 necklace 可換三角形は、元の同じ Serre 生成射と厳密に可換。 -/
lemma necklaceLambdaCell_relation {K : SSet.{u}} {x y : K _⦋0⦌}
    {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} (f : T ⟶ U) :
    (serreConcreteCubeComplexFunctor A).map (necklaceConcreteCubeMap f.necklaceHom) ≫
      necklaceLambdaCell A U = necklaceLambdaCell A T := by
  have h := congrArg ((cubicalSerreChains A).map) (necklaceCubicalCell_relation f)
  have ht := (cubicalSerreChainsCubeIso A).hom.naturality
    (necklaceConcreteCubeMap f.necklaceHom)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (cubicalSerreChains A).map (necklaceCubicalCell U)) ht).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => (cubicalSerreChainsCubeIso A).hom.app _ ≫ g)
          ((cubicalSerreChains A).map_comp _ _).symm).trans
            (congrArg (fun g => (cubicalSerreChainsCubeIso A).hom.app _ ≫ g) h))))

end SerrePositivity.KST.SConstruction
