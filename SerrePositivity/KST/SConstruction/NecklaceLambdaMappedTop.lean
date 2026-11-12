module
public import SerrePositivity.KST.SConstruction.NecklaceLambdaComposition
public import SerrePositivity.KST.SConstruction.SerreCubeTopMappedComposition

/-! # 元の連結生成射の実 dg 関手による最高生成元像
概要：元の連結 necklace の最高生成元像は、元の実 dg 関手の値で通常順合成になる。
方針：元の実鎖射の合成等号を、元の dg 合成保存付き最高生成元評価へ渡す。
規約：元の実 dg 入力と Hom 鎖射を保持。使われ方：HA 成分の分割合成像。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の連結生成射を実 dg 関手で送った最高生成元像は、同じ通常順合成。 -/
lemma necklaceLambdaCell_top_composition_post {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) D) {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    serreCubeTopCellImage A (homObject A D (F.obj x) (F.obj z))
        (T.necklace.down.dimension + U.necklace.down.dimension)
        (((serreConcreteCubeComplexFunctor A).map
          (necklaceCubeTensorIso T.necklace U.necklace).hom ≫
            necklaceLambdaCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U)) ≫ F.map x z) =
      compose A
        (serreCubeTopCellImage A (homObject A D (F.obj y) (F.obj z)) U.necklace.down.dimension
          (necklaceLambdaCell A U ≫ F.map y z))
        (serreCubeTopCellImage A (homObject A D (F.obj x) (F.obj y)) T.necklace.down.dimension
          (necklaceLambdaCell A T ≫ F.map x y)) (by omega) := by
  exact (congrArg
    (fun f => serreCubeTopCellImage A (homObject A D (F.obj x) (F.obj z))
      (T.necklace.down.dimension + U.necklace.down.dimension) (f ≫ F.map x z))
    (necklaceLambdaCell_composition A T U).symm).trans
      (serreCubeTopCellImage_composition_post A F T.necklace.down.dimension
        U.necklace.down.dimension (necklaceLambdaCell A T) (necklaceLambdaCell A U))

end SerrePositivity.KST.SConstruction
