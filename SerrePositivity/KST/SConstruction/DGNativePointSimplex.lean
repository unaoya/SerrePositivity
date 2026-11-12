module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
public import SerrePositivity.KST.SConstruction.CubicalLambdaPointPair
public import SerrePositivity.KST.SConstruction.DGNerveTensorSimplex

/-! # 元の固定 dg 対象の native 単体と tensor 包含
概要：元の増大と対象の閉単位から作る全単体族を、元の頂点の全退化と照合する。
方針：全 Λ 関手の厳密逆律と、元の固定対象の単位挿入による組の式を使う。
規約：全対象宇宙と全作用素を保持。使われ方：実 Perf 作用の固定入力の回収。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元の増大と指定対象の閉単位による native 定数単体。 -/
def dgNativePointSimplex (x : D) (N : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N :=
  cubicalLambdaNativeSimplex A
    (DGFunctor.comp (cubicalLambdaCounit A (Δ[N] : SSet.{u})) (DGQuotient.pointDGFunctor A D x))

/-- 元の native 定数単体は、退化を含む全作用素で同じ定数単体を回収する。 -/
lemma dgNativePointSimplex_pullback (x : D) {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1)) :
    (dgNativePointSimplex A D x N).pullback α = dgNativePointSimplex A D x M := by
  unfold dgNativePointSimplex
  rw [← cubicalLambdaNativeSimplex_precompose, ← strictDGFunctor_comp_assoc,
    cubicalLambdaCounit_naturality]

/-- 元の native 定数零単体は、指定した同じ対象の頂点。 -/
lemma dgNativePointSimplex_zero (x : D) :
    dgNativePointSimplex A D x 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- 元の native 定数単体との右 tensor は、元の固定対象の tensor 包含を回収する。 -/
lemma dgNerveTensorSimplex_point_right {C : Type w} [DGCategory A C] {N : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A C N) (x : D) :
    dgNerveTensorSimplex A s (dgNativePointSimplex A D x N) =
      s.map (dgTensorIncludeFirst A C D x) := by
  unfold dgNerveTensorSimplex dgNativePointSimplex
  rw [simplexHAInverseFunctor_native, cubicalLambdaFunctorPair_point_right,
    cubicalLambdaNativeSimplex_post, cubicalLambdaNativeSimplex_inverse]

end SerrePositivity.KST.SConstruction
