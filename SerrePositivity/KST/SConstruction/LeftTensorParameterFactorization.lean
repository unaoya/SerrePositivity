module
public import SerrePositivity.KST.SConstruction.LeftModuleParameterRepresentation
public import SerrePositivity.KST.SConstruction.LeftTensorParameterPullback

/-! # 元の左 tensor Hom 写像を通る任意パラメータの因子化
概要：任意 K の左 tensor 作用は、既存の左加群 Hom の射と実 tensor Hom 写像の合成。
方針：既存の Hom の普遍族に作用し、パラメータ引き戻しと currying の自然性を使う。
規約：元の実 tensor 射を保持する。使われ方：高次入力の単位・合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の任意パラメータの作用は、既存の実左 tensor Hom 写像を通って因子化する。 -/
lemma dgLeftParamHom_factorization {K : Complex A} {N N' : LeftModule A D}
    (M : RightModule A D) (τ : DGFunctorParamTrans A D (Complex A) K N N') :
    curryRight (BalancedTensor.leftParamMap A D M τ.app τ.naturality) =
      dgLeftModuleParameterHom A D τ ≫ BalancedTensor.leftHomMap A D M N N' := by
  have h := congrArg (fun σ : DGFunctorParamTrans A D (Complex A) K N N' =>
    curryRight (BalancedTensor.leftParamMap A D M σ.app σ.naturality))
      (dgLeftModuleParameter_factorization A D τ)
  rw [dgLeftParamMap_pullback] at h
  have hc := curryRight_naturality_source (dgLeftModuleParameterHom A D τ)
    (BalancedTensor.leftParamMap A D M
      (dgLeftModuleParameterUniversal A D (N := N) (N' := N')).app
      (dgLeftModuleParameterUniversal A D (N := N) (N' := N')).naturality)
  simp only [tensorHom_id] at hc
  exact h.symm.trans hc

end SerrePositivity.KST.SConstruction
