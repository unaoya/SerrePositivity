module
public import SerrePositivity.KST.SConstruction.LeftTensorParameterUnit
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions

/-! # bimodule の第一 tensor 変数の高次単位保存
概要：単位パラメータ自然変換は、元の tensor 合成の単位自然変換へ送られる。
方針：全 Hom 評価で左 tensor の既存単位法則へ帰着する。
規約：外側の対象全体の end や smallness を要求しない。使われ方：実延長の単位。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C] [DGCategory A E]

omit [Small.{u} C] in
/-- 左対象を固定した元の単位自然変換は、同じ値の単位自然変換である。 -/
lemma dgBimoduleParamLeftAt_identity (P : Bimodule A B C) (b : B) :
    Bimodule.paramLeftAt A B C (dgFunctorParamIdentity A C (RightModule A B) P.toFunctor) b =
      dgFunctorParamIdentity A C (Complex A) (P.leftAt b) := by
  apply GradedNatTrans.ext
  funext c
  exact moduleIdentity_π A B (P.rightAt c) b

/-- 元の第一 tensor 変数の作用は、全次数自然変換の単位を保持する。 -/
lemma dgFirstParam_identity (P : Bimodule A B C) (Q : Bimodule A C E) :
    BimoduleTensor.firstParam A B C E Q
        (dgFunctorParamIdentity A C (RightModule A B) P.toFunctor) =
      dgFunctorParamIdentity A E (RightModule A B)
        (BimoduleTensor.compose A B C E P Q).toFunctor := by
  apply GradedNatTrans.ext
  funext e
  apply moduleHom_ext
  intro b
  change Bimodule.paramValue A B E (BimoduleTensor.firstParam A B C E Q
      (dgFunctorParamIdentity A C (RightModule A B) P.toFunctor)) b e =
    moduleIdentity A B ((BimoduleTensor.compose A B C E P Q).rightAt e) ≫ _
  rw [BimoduleTensor.firstParam_value, moduleIdentity_π]
  have h := congrArg (fun σ : DGFunctorParamTrans A C (Complex A) (𝟙_ (Complex A))
      (P.leftAt b) (P.leftAt b) =>
    curryRight (BalancedTensor.leftParamMap A C (Q.rightAt e) σ.app σ.naturality))
      (dgBimoduleParamLeftAt_identity A B C P b)
  exact h.trans (dgLeftParamHom_identity A C (Q.rightAt e) (P.leftAt b))

end SerrePositivity.KST.SConstruction
