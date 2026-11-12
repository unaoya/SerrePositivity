module
public import SerrePositivity.KST.SConstruction.SimplexSubsetInteriorSum
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeFaceTerm

/-! # 元の HA 右辺の面座標による表示
概要：元の HA の内部頂点和を、同じ座標・次数の元の標準両面の差の和として回収する。
方針：元の内部頂点同値による和の移送と、各寄与・符号の同定を使う。
規約：元の実 dg 関手・全面の添字と符号を保持。使われ方：最高生成元微分との照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped BigOperators
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の native HA の右辺は、元の全ての面座標に対応する標準両面像の符号付き差の和。 -/
lemma cubicalLambdaNativeSimplexData_rhs_faces {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (cubicalLambdaNativeSimplexData A F).rhs I
        (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (2 - (I.card : ℤ)) hI rfl rfl rfl =
      ∑ i : Fin (I.card - 2),
        let j := simplexSubsetInteriorCoordinateEquiv I hI i
        ((i.val : ℤ) + 1).negOnePow •
          (simplexSubsetMappedFaceTopImage A false F I hI j.val j.property.1
              j.property.2.1 j.property.2.2 -
            simplexSubsetMappedFaceTopImage A true F I hI j.val j.property.1
              j.property.2.1 j.property.2.2) := by
  have hs := simplexSubset_sum_interior I hI
    (fun j hj hjm hjM => (cubicalLambdaNativeSimplexData A F).term I
      (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
      (2 - (I.card : ℤ)) hI rfl rfl rfl j hj hjm hjM)
  have he := (simplexSubsetInteriorCoordinateEquiv I hI).sum_comp
    (fun j : SimplexSubsetInterior I hI => (cubicalLambdaNativeSimplexData A F).term I
      (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
      (2 - (I.card : ℤ)) hI rfl rfl rfl j.val j.property.1 j.property.2.1 j.property.2.2)
  exact hs.trans (he.symm.trans (Finset.sum_congr rfl (fun i _ =>
    (cubicalLambdaNativeSimplexData_term_faces A F I hI _ _ _ _).trans
      (congrArg (fun s => s • (simplexSubsetMappedFaceTopImage A false F I hI
          (simplexSubsetInteriorCoordinateEquiv I hI i).val
          (simplexSubsetInteriorCoordinateEquiv I hI i).property.1
          (simplexSubsetInteriorCoordinateEquiv I hI i).property.2.1
          (simplexSubsetInteriorCoordinateEquiv I hI i).property.2.2 -
        simplexSubsetMappedFaceTopImage A true F I hI
          (simplexSubsetInteriorCoordinateEquiv I hI i).val
          (simplexSubsetInteriorCoordinateEquiv I hI i).property.1
          (simplexSubsetInteriorCoordinateEquiv I hI i).property.2.1
          (simplexSubsetInteriorCoordinateEquiv I hI i).property.2.2))
        (simplexSubsetCoordinateVertex_sign I hI i).symm))))

end SerrePositivity.KST.SConstruction
