module
public import SerrePositivity.KST.SConstruction.SimplexSubsetMappedOneFaceTop

/-! # 元の標準両面と native HA の内部頂点寄与
概要：元の native HA 内部頂点寄与を、同じ座標・出力次数の元の標準両面の差と同定。
方針：元の削除成分・合成成分の最高生成元回収を、元の符号付き寄与の式へ代入する。
規約：元の実 dg 関手と HA の右側頂点数符号を保持。使われ方：全面境界和の移送。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の HA の内部頂点寄与は、元の同座標の標準零面像と一面像の符号付き差そのもの。 -/
lemma cubicalLambdaNativeSimplexData_term_faces {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
    (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    (cubicalLambdaNativeSimplexData A F).term I
        (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (2 - (I.card : ℤ)) hI rfl rfl rfl j hj hjm hjM =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        (simplexSubsetMappedFaceTopImage A false F I hI j hj hjm hjM -
          simplexSubsetMappedFaceTopImage A true F I hI j hj hjm hjM) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.term_eq_linear_sub_cut,
    cubicalLambdaNativeSimplexData_erase_zero_face A F I hI j hj hjm hjM,
    cubicalLambdaNativeSimplexData_cutCompose_one_face A F I hI j hj hjm hjM]
  rfl

end SerrePositivity.KST.SConstruction
