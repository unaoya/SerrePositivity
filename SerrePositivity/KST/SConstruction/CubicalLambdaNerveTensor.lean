module
public import SerrePositivity.KST.SConstruction.CubicalLambdaFunctorPair
public import SerrePositivity.KST.SConstruction.CubicalLambdaNerveNativeIso
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-! # Λ nerve の直積から実 dg tensor への単体的比較
概要：全 Λ 関手の直積を、元の Serre 対角で実 dg tensor の nerve へ送る。
方針：元の全入力前合成との厳密な可換性を単体作用素の自然性に使う。
規約：直積は単体集合の直積、標的は実 tensor dg 圏。使われ方：native tensor 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]

/-- 元の全 Λ 関手の直積から、実 tensor dg 圏の Λ nerve への実単体的写像。 -/
def cubicalLambdaNerveTensor :
    cubicalLambdaNerve A D ⊗ cubicalLambdaNerve A E ⟶
      cubicalLambdaNerve A (DGTensorCategory A D E) where
  app _ := ↾fun p => cubicalLambdaFunctorPair A p.1 p.2
  naturality X Y f := by
    ext p
    exact cubicalLambdaFunctorPair_precompose A (SSet.stdSimplex.map f.unop) p.1 p.2

/-- 直積から実 tensor への比較の各次数は、元の Serre 対角による関手の組。 -/
lemma cubicalLambdaNerveTensor_app {N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (G : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) E) :
    (cubicalLambdaNerveTensor A D E).app (op ⦋N⦌) (F, G) =
      cubicalLambdaFunctorPair A F G := rfl

/-- native dg nerve の直積から実 tensor dg 圏の native nerve への実単体的比較。 -/
def dgNerveTensor : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGTensorCategory A D E) :=
  ((cubicalLambdaNerveNativeIso A D).inv ⊗ₘ (cubicalLambdaNerveNativeIso A E).inv) ≫
    cubicalLambdaNerveTensor A D E ≫
      (cubicalLambdaNerveNativeIso A (DGTensorCategory A D E)).hom

/-- native 比較は、両方の実逆 dg 関手を対角で組にして native 単体へ戻す。 -/
lemma dgNerveTensor_app {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E N) :
    (dgNerveTensor A D E).app (op ⦋N⦌) (s, t) =
      cubicalLambdaNativeSimplex A
        (cubicalLambdaFunctorPair A (simplexHAInverseFunctor A s) (simplexHAInverseFunctor A t)) :=
  rfl

end SerrePositivity.KST.SConstruction
