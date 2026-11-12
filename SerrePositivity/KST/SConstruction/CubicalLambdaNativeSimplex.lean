module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeDifferentialBoundary
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeEdgeEquation

/-! # 元の Λ 標準単体からの実 dg 関手の native dg nerve 単体
概要：元の実 dg 関手の全成分が HA の全方程式を満たし、元の native 単体を定める。
方針：元の全面微分と元の内部頂点和を同じ面像和で比較し、二点の既存方程式と合わせる。
規約：元の指定端点・次数・実 dg 関手を保持。使われ方：native dg nerve と Λ の比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の実 dg 関手から回収した全成分は、指定端点・次数で全ての HA 方程式を満たす。 -/
lemma cubicalLambdaNativeSimplexData_equation {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ)) :
    differential A ((cubicalLambdaNativeSimplexData A F).hom I a b k hI ha hb hk) =
      (cubicalLambdaNativeSimplexData A F).rhs I a b k hI ha hb hk := by
  by_cases h2 : I.card = 2
  · exact cubicalLambdaNativeSimplexData_equation_two A F I a b k hI ha hb hk h2
  · have h3 : 3 ≤ I.card := by omega
    subst a
    subst b
    subst k
    exact (cubicalLambdaNativeSimplexData_differential_uniform_faces A F I hI h3).trans
      (cubicalLambdaNativeSimplexData_rhs_uniform_faces A F I hI h3).symm

/-- 元の Λ 標準単体からの実 dg 関手が定める、元の HA 全方程式を持つ native 単体。 -/
def cubicalLambdaNativeSimplex {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n where
  toSimplexData := cubicalLambdaNativeSimplexData A F
  equation := cubicalLambdaNativeSimplexData_equation A F

/-- 元の native 単体のデータは、元の実 dg 関手からの同じ全成分データ。 -/
lemma cubicalLambdaNativeSimplex_toSimplexData {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D) :
    (cubicalLambdaNativeSimplex A F).toSimplexData = cubicalLambdaNativeSimplexData A F := rfl

/-- 元の native 単体の回収は、元の実 dg 関手の後合成と厳密に可換。 -/
lemma cubicalLambdaNativeSimplex_post {n : ℕ} {E : Type w} [DGCategory A E]
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D) (G : DGFunctor A D E) :
    cubicalLambdaNativeSimplex A (DGFunctor.comp F G) = (cubicalLambdaNativeSimplex A F).map G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (cubicalLambdaNativeSimplexData_post A F G)

end SerrePositivity.KST.SConstruction
