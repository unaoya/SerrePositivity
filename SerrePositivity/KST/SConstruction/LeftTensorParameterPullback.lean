module
public import SerrePositivity.KST.SConstruction.DGParameterPullback
public import SerrePositivity.KST.SConstruction.DGParameterCrossNaturality
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-! # 左 tensor パラメータ作用の引き戻し
概要：パラメータ複体の射と、元の balanced tensor の作用が可換である。
方針：元の balanced 族で横断と逆転置を照合し、同じ coend の降下を使う。
規約：元のパラメータと交差順を保持する。使われ方：graph 延長の高次入力の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  {K L : Complex A} {N N' : LeftModule A D}
  (a : L ⟶ K) (M : RightModule A D) (τ : DGFunctorParamTrans A D (Complex A) K N N')

/-- パラメータ射による引き戻しは、元の左 tensor の balanced 族の引き戻し。 -/
lemma dgLeftParamFamily_pullback :
    BalancedTensor.leftParamFamily A D M (dgParameterPullback A a τ).app
        (dgParameterPullback A a τ).naturality =
      BalancedTensor.paramPrecompose A D M N a
        (BalancedTensor.leftParamFamily A D M τ.app τ.naturality) := by
  apply Subtype.ext
  funext d
  change parameterCross L (M.obj (op d)) (N.obj d) ≫
        (M.obj (op d) ◁ uncurryRight (a ≫ τ.app d)) ≫ BalancedTensor.ι A D M N' d =
      (a ▷ (M.obj (op d) ⊗ N.obj d)) ≫ parameterCross K (M.obj (op d)) (N.obj d) ≫
        (M.obj (op d) ◁ uncurryRight (τ.app d)) ≫ BalancedTensor.ι A D M N' d
  rw [uncurryRight_precompose, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    ← dgParameterCross_naturality_assoc]

/-- 元の coend のパラメータ作用は、パラメータの chain map と可換。 -/
lemma dgLeftParamMap_pullback :
    BalancedTensor.leftParamMap A D M (dgParameterPullback A a τ).app
        (dgParameterPullback A a τ).naturality =
      (a ▷ BalancedTensor.obj A D M N) ≫
        BalancedTensor.leftParamMap A D M τ.app τ.naturality := by
  unfold BalancedTensor.leftParamMap
  rw [dgLeftParamFamily_pullback, BalancedTensor.paramDesc_precompose]

end SerrePositivity.KST.SConstruction
