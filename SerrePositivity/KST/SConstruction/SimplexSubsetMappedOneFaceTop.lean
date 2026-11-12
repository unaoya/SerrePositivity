module
public import SerrePositivity.KST.SConstruction.SimplexSubsetMappedFaceTop
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitFlatNormalization
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitNativeComposition

/-! # 元の標準一面の最高生成元像と native 合成項
概要：元の標準零面と同じ座標の標準一面の像を、同じ HA 出力次数の合成項と同定。
方針：元の実分割鎖射を平坦次元へ移し、元の最高生成元の次元移送を適用する。
規約：元の標準一面・実 dg 関手・指定出力次数を保持。使われ方：全高次 HA 方程式。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の native HA 合成項は、元の同じ標準一面の指定出力次数の最高生成元像。 -/
lemma cubicalLambdaNativeSimplexData_cutCompose_one_face {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
    (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    (cubicalLambdaNativeSimplexData A F).cutCompose I
        (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (2 - (I.card : ℤ)) j =
      simplexSubsetMappedFaceTopImage A true F I hI j hj hjm hjM := by
  let hL := simplexSubsetSplitLeft_two I hI j hj hjm
  let hR := simplexSubsetSplitRight_two I hI j hj hjM
  let T := necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL
  let U := necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR
  let a := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
  let b := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
  let H := homObject A D (F.obj a) (F.obj b)
  let d := T.necklace.down.dimension + U.necklace.down.dimension
  have hd : (I.erase j).card - 2 = d :=
    (simplexSubsetSplit_flat_erase_dimension I hI j hj hjm hjM).symm
  have hm : -(((I.erase j).card - 2 : ℕ) : ℤ) = (2 - (I.card : ℤ)) + 1 := by
    have he := simplexSubsetErase_two I hI j hjm hjM
    have hc := Finset.card_erase_add_one hj
    omega
  have hn : -(d : ℤ) = (2 - (I.card : ℤ)) + 1 :=
    simplexSubsetSplit_degree.{u} I hI j hj hL hR
  let f := (serreConcreteCubeComplexFunctor A).map
    (necklaceCubeTensorIso T.necklace U.necklace).hom ≫
      necklaceLambdaCell A (necklaceInSimplexSubsetSplit I hI j hj hL hR)
  let g := F.map a b
  let r := eqToHom (congrArg H.X hn) (serreCubeTopCellImage A H d (f ≫ g))
  have hN : (cubicalLambdaNativeSimplexData A F).cutCompose I
      (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
      (2 - (I.card : ℤ)) j = r := by
    exact (cubicalLambdaNativeSimplexData_cutCompose A F I hI j hj hL hR).trans
      (congrArg (fun l => eqToHom (congrArg H.X hn)
        (serreCubeTopCellImage A H d
          (((serreConcreteCubeComplexFunctor A).map
            (necklaceCubeTensorIso T.necklace U.necklace).hom ≫ l) ≫ g)))
        (simplexSubsetSplitLambdaCell_relation A I hI j hj hL hR))
  have hF : simplexSubsetMappedFaceTopImage A true F I hI j hj hjm hjM = r := by
    exact (congrArg (fun l => eqToHom (congrArg H.X hm)
      (serreCubeTopCellImage A H ((I.erase j).card - 2) (l ≫ g)))
      (simplexSubsetLambdaSplit_flat_one_face I hI j hj hjm hjM A)).trans
        (serreCubeTopCellImage_cast_dimension_post A hd _ hm hn f g)
  exact hN.trans hF.symm

end SerrePositivity.KST.SConstruction
