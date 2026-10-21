module
public import SerrePositivity.KST.SConstruction.DGComposeDegreeTransport
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitDegrees
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitMappedTop
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaGeneratorNecklace
public import SerrePositivity.InfinityCategories.DGNerve.BoundaryDecomposition

/-! # 元の実分割最高生成元像と native HA 合成項
概要：元の実分割射の最高生成元像を、元の native HA 合成項そのものとして回収する。
方針：元の左右成分の回収・次数移送と通常順合成の交換を合成する。
規約：元の部分集合・dg 関手・出力次数を保持。使われ方：全高次 HA 方程式の非線形項。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の実分割射の最高生成元像を、元の HA 合成項の次数で読む。 -/
def simplexSubsetSplitMappedTopImage {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (homObject A D
      (F.obj (standardSimplexVertex (I.min' (simplexSubsetNonempty I hI))))
      (F.obj (standardSimplexVertex (I.max' (simplexSubsetNonempty I hI))))).X
        ((2 - (I.card : ℤ)) + 1) :=
  eqToHom (congrArg (fun k => (homObject A D
    (F.obj (standardSimplexVertex (I.min' (simplexSubsetNonempty I hI))))
    (F.obj (standardSimplexVertex (I.max' (simplexSubsetNonempty I hI))))).X k)
      (simplexSubsetSplit_degree.{u} I hI j hj hL hR))
    (serreCubeTopCellImage A _
      ((necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL).necklace.down.dimension +
        (necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR).necklace.down.dimension)
      (((serreConcreteCubeComplexFunctor A).map (necklaceCubeTensorIso
        (necklaceInSimplexSubsetSplitLeft.{u} I hI j hj hL).necklace
        (necklaceInSimplexSubsetSplitRight.{u} I hI j hj hR).necklace).hom ≫
        (serreConcreteCubeComplexFunctor A).map
          (necklaceConcreteCubeMap (simplexSubsetSplitRefinement I j hj hL hR)) ≫
            necklaceLambdaCell A (necklaceInSimplexSubset I hI)) ≫
        F.map (standardSimplexVertex (I.min' (simplexSubsetNonempty I hI)))
          (standardSimplexVertex (I.max' (simplexSubsetNonempty I hI)))))

/-- 元の native HA 合成項は、元の実分割射の同じ最高生成元像そのもの。 -/
lemma cubicalLambdaNativeSimplexData_cutCompose {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hL : 2 ≤ (I.filter (· ≤ j)).card) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (cubicalLambdaNativeSimplexData A F).cutCompose I
        (I.min' (simplexSubsetNonempty I hI)) (I.max' (simplexSubsetNonempty I hI))
        (2 - (I.card : ℤ)) j = simplexSubsetSplitMappedTopImage A F I hI j hj hL hR := by
  have hl := necklaceInSimplexSubsetSplitLeft_dimension.{u} I hI j hj hL
  have hr := necklaceInSimplexSubsetSplitRight_dimension.{u} I hI j hj hR
  have hc := DGNerve.Index.split_card hj
  have hs : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = (2 - (I.card : ℤ)) + 1 := by omega
  have hla := DGNerve.Index.left_min (I.isLeast_min' (simplexSubsetNonempty I hI))
    (I.min'_le j hj) (simplexSubsetNonempty _ hL)
  have hlb := DGNerve.Index.left_max hj (simplexSubsetNonempty _ hL)
  have hra := DGNerve.Index.right_min hj (simplexSubsetNonempty _ hR)
  have hrb := DGNerve.Index.right_max (I.isGreatest_max' (simplexSubsetNonempty I hI))
    (I.le_max' j hj) (simplexSubsetNonempty _ hR)
  unfold DGNerve.SimplexData.cutCompose
  rw [dite_eq_left hs]
  rw [DGNerve.SimplexData.homOrZero_eq _ _ _ _ _ hR hra hrb rfl,
    DGNerve.SimplexData.homOrZero_eq _ _ _ _ _ hL hla hlb rfl]
  rw [cubicalLambdaNativeSimplexData_hom_necklace,
    cubicalLambdaNativeSimplexData_hom_necklace]
  exact ((congrArg (fun w => eqToHom (congrArg (fun k => (homObject A D
      (F.obj (standardSimplexVertex (I.min' (simplexSubsetNonempty I hI))))
      (F.obj (standardSimplexVertex (I.max' (simplexSubsetNonempty I hI))))).X k)
      (simplexSubsetSplit_degree.{u} I hI j hj hL hR)) w)
    (simplexSubsetSplit_top_composition_post A F I hI j hj hL hR)).trans
      (dgCompose_degree_transport A (by omega) (by omega)
        (simplexSubsetSplit_degree.{u} I hI j hj hL hR) _ _ (by omega) hs)).symm

end SerrePositivity.KST.SConstruction
