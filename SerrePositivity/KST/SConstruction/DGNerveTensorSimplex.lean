module
public import SerrePositivity.KST.SConstruction.DGNerveTensorUnits
public import SerrePositivity.KST.SConstruction.DGNerveTensorAssociativity

/-! # 異なる対象宇宙の native tensor 単体と元の単位単体
概要：実 tensor 比較の各単体を、二入力の対象宇宙が異なる場合にも定義する。
方針：全 Hom を復元する逆 dg 関手を Serre 対角で組にし、元の native 単体に戻す。
規約：元の一対象 A を使い、全作用素を保つ。使われ方：tensor 比較の単位との照合。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- 異なる対象宇宙も許す、元の Serre 対角による native tensor 単体。 -/
def dgNerveTensorSimplex {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGTensorCategory A D E) N :=
  cubicalLambdaNativeSimplex A
    (cubicalLambdaFunctorPair A (simplexHAInverseFunctor A s) (simplexHAInverseFunctor A t))

/-- 各単体での比較は、退化を含む元の全単体作用素と厳密に可換。 -/
lemma dgNerveTensorSimplex_pullback {M N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E N) (α : Fin (M + 1) →o Fin (N + 1)) :
    dgNerveTensorSimplex A (s.pullback α) (t.pullback α) =
      (dgNerveTensorSimplex A s t).pullback α := by
  unfold dgNerveTensorSimplex
  rw [simplexHAInverseFunctor_pullback, simplexHAInverseFunctor_pullback,
    cubicalLambdaFunctorPair_precompose, cubicalLambdaNativeSimplex_precompose]

/-- 対象宇宙が共通なら、各単体の tensor 比較は元の実単体的写像そのもの。 -/
lemma dgNerveTensorSimplex_app {B : Type v} [DGCategory A B] {N : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A B N) :
    dgNerveTensorSimplex A s t = (dgNerveTensor A D B).app (op ⦋N⦌) (s, t) := rfl

/-- 元の増大 dg 関手から作る、一対象 A の native 単位単体。 -/
def dgNerveUnitSimplex (N : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A PUnit.{1} N :=
  cubicalLambdaNativeSimplex A (cubicalLambdaCounit A (Δ[N] : SSet.{u}))

/-- 元の native 単位単体は、退化を含む全単体作用素で同じ単位単体を回収する。 -/
lemma dgNerveUnitSimplex_pullback {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1)) :
    (dgNerveUnitSimplex A N).pullback α = dgNerveUnitSimplex A M := by
  unfold dgNerveUnitSimplex
  rw [← cubicalLambdaNativeSimplex_precompose, cubicalLambdaCounit_naturality]

/-- 単位単体との左 tensor は、元の全作用素を保つ左単位挿入そのもの。 -/
lemma dgNerveTensorSimplex_unit_left {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) :
    dgNerveTensorSimplex A (dgNerveUnitSimplex A N) s =
      (dgNerveUnitLeft A D).app (op ⦋N⦌) s := by
  unfold dgNerveTensorSimplex dgNerveUnitSimplex
  rw [simplexHAInverseFunctor_native]
  rfl

/-- 単位単体との右 tensor は、元の全作用素を保つ右単位挿入そのもの。 -/
lemma dgNerveTensorSimplex_unit_right {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) :
    dgNerveTensorSimplex A s (dgNerveUnitSimplex A N) =
      (dgNerveUnitRight A D).app (op ⦋N⦌) s := by
  unfold dgNerveTensorSimplex dgNerveUnitSimplex
  rw [simplexHAInverseFunctor_native]
  rfl

/-- 元の単位単体との左 tensor を実左単位関手で戻すと、元の native 単体となる。 -/
lemma dgNerveTensorSimplex_left_unitor {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) :
    (dgNerveTensorSimplex A (dgNerveUnitSimplex A N) s).map (dgTensorLeftUnitor A D) = s := by
  rw [dgNerveTensorSimplex_unit_left]
  exact congrFun (congrArg (fun f => f.app (op ⦋N⦌)) (dgNerveUnitLeft_unitor A D)) s

/-- 元の単位単体との右 tensor を実右単位関手で戻すと、元の native 単体となる。 -/
lemma dgNerveTensorSimplex_right_unitor {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) :
    (dgNerveTensorSimplex A s (dgNerveUnitSimplex A N)).map (dgTensorRightUnitor A D) = s := by
  rw [dgNerveTensorSimplex_unit_right]
  exact congrFun (congrArg (fun f => f.app (op ⦋N⦌)) (dgNerveUnitRight_unitor A D)) s

end SerrePositivity.KST.SConstruction
