module
public import SerrePositivity.KST.SConstruction.CubicalSerreGeneratorTensor
public import SerrePositivity.KST.SConstruction.NecklaceLambdaCell
public import SerrePositivity.KST.SConstruction.NecklaceCubicalComposition
public import SerrePositivity.KST.SConstruction.CubicalSerreComonoidCells

/-! # 元の全 necklace 生成射の実 Serre 合成
概要：元の二つの Serre 生成射の豊穣合成を、元の連結 necklace の生成射と同定する。
方針：元の表現可能 Day tensor 比較と Serre 生成射の tensor 則を合成する。
規約：元の鎖複体・順序・合成射を保持。使われ方：HA の分割合成項の実最高生成元。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の両 necklace の合成は、連結立方体の元の生成射と実 tensor 比較を回収する。 -/
lemma necklaceCubicalCompose_generator {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    cubicalDayCubeInclusion (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.necklace.down.dimension)
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk U.necklace.down.dimension) ≫
      cubicalDayTensorMap (necklaceCubicalCell T) (necklaceCubicalCell U) ≫
        necklaceCubicalCompose K x y z =
      cubicalYoneda.map (necklaceCubeTensorIso T.necklace U.necklace).hom ≫
        necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U) := by
  rw [necklaceCubicalCompose_cell]
  change cubicalDayCubeInclusion _ _ ≫
    ((cubicalDayCubeProjection _ _ ≫
      cubicalYoneda.map (necklaceCubeTensorIso T.necklace U.necklace).hom) ≫
      necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U)) = _
  erw [Category.assoc, ← Category.assoc (cubicalDayCubeInclusion _ _),
    cubicalDayCubeInclusion_projection, Category.id_comp]

/-- 元の Serre 分割・両生成射・豊穣合成は、元の連結生成射と実次元移送を回収する。 -/
lemma necklaceLambdaCell_composition {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    (serreCubeTensorIso A T.necklace.down.dimension U.necklace.down.dimension).hom.hom ≫
      (necklaceLambdaCell A T ⊗ₘ necklaceLambdaCell A U) ≫
        eComp (Complex A) (C := CubicalLambda A K) x y z =
      (serreConcreteCubeComplexFunctor A).map (necklaceCubeTensorIso T.necklace U.necklace).hom ≫
        necklaceLambdaCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U) := by
  have ht := cubicalSerreGenerator_tensor A (necklaceCubicalCell T) (necklaceCubicalCell U)
  have hc := necklaceCubicalCompose_generator T U
  have hg := cubicalSerreGenerator_relation A
    (necklaceCubeTensorIso T.necklace U.necklace).hom
    (necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U))
  have hn := cubicalSerreGenerator_naturality A (necklaceCubicalCompose K x y z)
    (cubicalDayCubeInclusion _ _ ≫
      cubicalDayTensorMap (necklaceCubicalCell T) (necklaceCubicalCell U))
  have hd : Functor.OplaxMonoidal.δ (serreConcreteCubeComplexFunctor A)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.necklace.down.dimension) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk U.necklace.down.dimension) =
      (serreCubeTensorIso A T.necklace.down.dimension U.necklace.down.dimension).hom.hom :=
    (serreConcreteCubeComplex_cotensorator_hom A _ _).trans rfl
  rw [hd] at ht
  have he : eComp (Complex A) (C := CubicalLambda A K) x y z =
      cubicalSerreDayInverse A (necklaceCubicalMapping K x y) (necklaceCubicalMapping K y z) ≫
        (cubicalSerreChains A).map (necklaceCubicalCompose K x y z) := rfl
  erw [he, ← Category.assoc (necklaceLambdaCell A T ⊗ₘ necklaceLambdaCell A U)]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cubicalSerreChains A).map (necklaceCubicalCompose K x y z))
      ht).trans (hn.trans
        ((congrArg (cubicalSerreGenerator A) ((Category.assoc _ _ _).trans hc)).trans hg.symm)))

end SerrePositivity.KST.SConstruction
