module
public import SerrePositivity.KST.SConstruction.LeftTensorParameterFactorization
public import SerrePositivity.DifferentialGraded.Tensor.Enriched

/-! # 左 tensor の Yoneda 評価の任意パラメータ自然性
概要：代表右加群との tensor の Yoneda 評価は、任意複体 K の左加群変換と可換。
方針：元のパラメータ作用を既存左加群 Hom で表示し、全 Hom の評価自然性を使う。
規約：元の coend・Yoneda 評価・パラメータを保つ。使われ方：右単位比較の入力自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の全パラメータ作用は、同じ tensor Yoneda 評価の前後で厳密に可換。 -/
lemma dgLeftParamHom_yoneda_naturality {K : Complex A} {N N' : LeftModule A D}
    (τ : DGFunctorParamTrans A D (Complex A) K N N') (d : D) :
    curryRight (BalancedTensor.leftParamMap A D (representable A d) τ.app τ.naturality) ≫
        homPostcompose (BalancedTensor.obj A D (representable A d) N)
          (BalancedTensor.yonedaEvaluation A D d N') =
      τ.app d ≫ homPrecompose (BalancedTensor.yonedaEvaluation A D d N) (N'.obj d) := by
  rw [dgLeftParamHom_factorization, Category.assoc,
    BalancedTensor.yonedaEvaluation_enriched_naturality, ← Category.assoc,
    dgLeftModuleParameterHom_π]

end SerrePositivity.KST.SConstruction
