module
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaCell
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping

/-! # 元の Λ 標準単体からの dg 関手の native HA 成分データ
概要：元の実 dg 関手から、元の有限部分集合の生成元の像で native な全成分を取り出す。
方針：同じ最小・最大端点と次数 2−濃度の元を、元の dg Hom 射で送る。
規約：HA 方程式は後続で証明する。使われ方：native dg nerve との元の単体比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の Λ 標準単体からの実 dg 関手の、元の全 HA 部分集合成分データ。 -/
def cubicalLambdaNativeSimplexData {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n where
  obj a := F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)
  hom I a b k hI ha hb hk := by
    subst a
    subst b
    subst k
    exact (F.map _ _).f (2 - (I.card : ℤ)) (simplexSubsetLambdaGenerator A I hI)

/-- 元の成分データの対象は、同じ番号の元の零単体への dg 関手の値。 -/
lemma cubicalLambdaNativeSimplexData_obj {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D) (a : Fin (n + 1)) :
    (cubicalLambdaNativeSimplexData A F).obj a = F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) := rfl

/-- 元の全部分集合成分は、同じ元の生成元に元の実 dg Hom 射を作用させた像。 -/
lemma cubicalLambdaNativeSimplexData_hom {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (cubicalLambdaNativeSimplexData A F).hom I
        (I.min' (Finset.card_pos.mp (by omega))) (I.max' (Finset.card_pos.mp (by omega)))
        (2 - (I.card : ℤ)) hI rfl rfl rfl =
      (F.map _ _).f (2 - (I.card : ℤ)) (simplexSubsetLambdaGenerator A I hI) := rfl

/-- 元の native 成分データの抽出は、実 dg 関手の後合成と厳密に可換。 -/
lemma cubicalLambdaNativeSimplexData_post {n : ℕ} {E : Type w} [DGCategory A E]
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D) (G : DGFunctor A D E) :
    cubicalLambdaNativeSimplexData A (DGFunctor.comp F G) =
      (cubicalLambdaNativeSimplexData A F).map G := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    subst a
    subst b
    subst k
    rfl

end SerrePositivity.KST.SConstruction
