module
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImageTransport
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitLambdaCell
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeSimplexData

/-! # 元の部分集合 necklace と native HA 成分の回収
概要：元の部分集合 necklace の最高生成元像を、元の HA 次数の生成元・成分と同定する。
方針：元の数値次元移送を最高生成元に適用し、元の dg Hom 鎖射と移送を交換する。
規約：元の指定端点・次数・dg 関手を保持。使われ方：分割合成像から native HA 合成項へ。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の部分集合の HA 生成元は、元の necklace 生成射の最高生成元像の次数移送。 -/
lemma simplexSubsetLambdaGenerator_necklace {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) :
    simplexSubsetLambdaGenerator A I hI =
      eqToHom (congrArg (fun k => (homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))).X k)
        (show -((necklaceInSimplexSubset.{u} I hI).necklace.down.dimension : ℤ) =
          2 - (I.card : ℤ) from by
            have hd := necklaceInSimplexSubset_dimension.{u} I hI
            omega))
        (serreCubeTopCellImage A _ (necklaceInSimplexSubset.{u} I hI).necklace.down.dimension
          (necklaceLambdaCell A (necklaceInSimplexSubset I hI))) := by
  unfold simplexSubsetLambdaGenerator
  rw [← simplexSubsetLambdaCell_necklace]
  exact serreCubeTopCellImage_cast_dimension A
    (necklaceInSimplexSubset_dimension.{u} I hI).symm _ (by omega)
    (by have hd := necklaceInSimplexSubset_dimension.{u} I hI; omega) _

/-- 元の native HA 成分は、元の指定端点 necklace と実 dg Hom 射の最高生成元像。 -/
lemma cubicalLambdaNativeSimplexData_hom_necklace {D : Type v} [DGCategory A D] {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ)) :
    (cubicalLambdaNativeSimplexData A F).hom I a b k hI ha hb hk =
      eqToHom (congrArg (fun d => (homObject A D
        (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))).X d)
        (show -((necklaceInSimplexSubsetAt.{u} I a b hI ha hb).necklace.down.dimension : ℤ) = k
          from by
            have hd := necklaceInSimplexSubset_dimension.{u} I hI
            change -((necklaceInSimplexSubset.{u} I hI).necklace.down.dimension : ℤ) = k
            omega))
        (serreCubeTopCellImage A _
          (necklaceInSimplexSubsetAt.{u} I a b hI ha hb).necklace.down.dimension
          (necklaceLambdaCell A (necklaceInSimplexSubsetAt I a b hI ha hb) ≫
            F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))) := by
  subst a
  subst b
  subst k
  change (F.map _ _).f _ (simplexSubsetLambdaGenerator A I hI) = _
  rw [simplexSubsetLambdaGenerator_necklace]
  exact serreCubeTopCellImage_cast_post A _ _
    (by have hd := necklaceInSimplexSubset_dimension.{u} I hI; omega) _ _

end SerrePositivity.KST.SConstruction
