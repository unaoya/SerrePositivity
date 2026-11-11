module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeNormalizedComponent
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaEraseFace
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearBoundary

/-! # 元の標準面の最高生成元像と native 削除成分
概要：元の標準面の最高生成元像を HA 出力次数で読み、零面の像を元の削除成分と同定。
方針：元の実鎖零面の回収式を、元の実 dg Hom 射と最高生成元評価へ送る。
規約：元の面座標・次元移送・指定端点を保持。使われ方：全高次 HA 方程式の線形項。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の標準面の最高生成元像を、元の HA 出力次数で読む。 -/
def simplexSubsetMappedFaceTopImage {n : ℕ} (b : Bool)
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
    (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    (homObject A D
      (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))
      (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))).X
        ((2 - (I.card : ℤ)) + 1) :=
  eqToHom (congrArg (fun k => (homObject A D
    (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))
    (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))).X k)
      (show -(((I.erase j).card - 2 : ℕ) : ℤ) = (2 - (I.card : ℤ)) + 1 by
        have he := simplexSubsetErase_two I hI j hjm hjM
        have hc := Finset.card_erase_add_one hj
        omega))
    (serreCubeTopCellImage A _ ((I.erase j).card - 2)
      (((serreCubeFace A b ((I.erase j).card - 2)
          (Fin.cast (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)
            (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM))).hom ≫
        (serreConcreteCubeComplexFunctor A).map
          (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
            (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((I.erase j).card - 2 + 1))
            (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM)).inv ≫
          simplexSubsetLambdaCell A I hI) ≫
        F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))))

/-- 元の native 削除成分は、元の標準零面の同じ HA 出力次数の最高生成元像。 -/
lemma cubicalLambdaNativeSimplexData_erase_zero_face {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
    (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    (cubicalLambdaNativeSimplexData A F).homOrZero (I.erase j)
        (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        ((2 - (I.card : ℤ)) + 1) =
      simplexSubsetMappedFaceTopImage A false F I hI j hj hjm hjM := by
  have he := simplexSubsetErase_two I hI j hjm hjM
  have hc := Finset.card_erase_add_one hj
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq _ _ _ _ _ he
    (simplexSubsetErase_min I hI j hjm hjM).symm
    (simplexSubsetErase_max I hI j hjm hjM).symm (by omega)]
  rw [cubicalLambdaNativeSimplexData_hom_normalized]
  exact (congrArg (fun f => eqToHom (congrArg (fun k => (homObject A D
      (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))
      (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))).X k)
      (show -(((I.erase j).card - 2 : ℕ) : ℤ) = (2 - (I.card : ℤ)) + 1 by omega))
    (serreCubeTopCellImage A _ ((I.erase j).card - 2)
      (f ≫ F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))))
    (simplexSubsetLambdaErase_zero_face I hI j hj hjm hjM A)).symm

end SerrePositivity.KST.SConstruction
