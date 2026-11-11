module
public import SerrePositivity.KST.SConstruction.NecklaceLambdaComposition
public import SerrePositivity.KST.SConstruction.SerreCubeTopCompositionImage

/-! # 元の連結 Serre 生成射の最高生成元
概要：元の necklace の実連結生成射の最高生成元像を、native 通常順の合成として読む。
方針：元の鎖射の合成等号と、既存の向き付き tensor 最高生成元評価を使う。
規約：元の次数と因子順を保持。使われ方：HA の部分集合分割合成項。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の実連結 Serre 生成射の向き付き最高生成元像は、元の通常順合成そのもの。 -/
lemma necklaceLambdaCell_top_composition {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    serreCubeTopCellImage A (homObject A (CubicalLambda A K) x z)
        (T.necklace.down.dimension + U.necklace.down.dimension)
        ((serreConcreteCubeComplexFunctor A).map
          (necklaceCubeTensorIso T.necklace U.necklace).hom ≫
            necklaceLambdaCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U)) =
      compose A
        (serreCubeTopCellImage A (homObject A (CubicalLambda A K) y z)
          U.necklace.down.dimension (necklaceLambdaCell A U))
        (serreCubeTopCellImage A (homObject A (CubicalLambda A K) x y)
          T.necklace.down.dimension (necklaceLambdaCell A T)) (by omega) := by
  exact (congrArg
    (serreCubeTopCellImage A (homObject A (CubicalLambda A K) x z)
      (T.necklace.down.dimension + U.necklace.down.dimension))
    (necklaceLambdaCell_composition A T U).symm).trans
      (serreCubeTopCellImage_composition A T.necklace.down.dimension U.necklace.down.dimension
        (necklaceLambdaCell A T) (necklaceLambdaCell A U))

end SerrePositivity.KST.SConstruction
