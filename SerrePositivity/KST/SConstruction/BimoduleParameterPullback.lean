module
public import SerrePositivity.KST.SConstruction.LeftTensorParameterPullback
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions

/-! # bimodule の第一 tensor 変数のパラメータ引き戻し
概要：任意のパラメータ射と、元の bimodule tensor 作用が可換である。
方針：左対象評価で balanced tensor の引き戻しへ帰着し、全 Hom で反映する。
規約：外側の対象型に smallness を要求しない。使われ方：実加群延長の高次整合性。
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
  {K L : Complex A} {P P' : Bimodule A B C}
  (a : L ⟶ K) (τ : BimoduleParamTrans A B C K P P')

omit [Small.{u} C] in
/-- 左対象の評価とパラメータの引き戻しは、全 Hom 成分で可換。 -/
lemma dgBimoduleParamLeftAt_pullback (b : B) :
    Bimodule.paramLeftAt A B C (dgParameterPullback A a τ) b =
      dgParameterPullback A a (Bimodule.paramLeftAt A B C τ b) := by
  apply GradedNatTrans.ext
  funext c
  exact Category.assoc _ _ _

/-- 第一 tensor 変数の Hom 成分は、パラメータの chain map と可換。 -/
lemma dgFirstParamHom_pullback (Q : Bimodule A C E) (b : B) (e : E) :
    BimoduleTensor.firstParamHom A B C E Q (dgParameterPullback A a τ) b e =
      a ≫ BimoduleTensor.firstParamHom A B C E Q τ b e := by
  unfold BimoduleTensor.firstParamHom BimoduleTensor.firstParamValue
  have h := congrArg (fun σ : DGFunctorParamTrans A C (Complex A) L (P.leftAt b) (P'.leftAt b) =>
    curryRight (BalancedTensor.leftParamMap A C (Q.rightAt e) σ.app σ.naturality))
      (dgBimoduleParamLeftAt_pullback A B C a τ b)
  rw [dgLeftParamMap_pullback] at h
  exact h.trans (by
    simpa only [tensorHom_id] using curryRight_naturality_source a
      (BalancedTensor.leftParamMap A C (Q.rightAt e)
        (Bimodule.paramLeftAt A B C τ b).app (Bimodule.paramLeftAt A B C τ b).naturality))

/-- 元の第一 tensor 変数の全パラメータ作用は、引き戻しと可換。 -/
lemma dgFirstParam_pullback (Q : Bimodule A C E) :
    BimoduleTensor.firstParam A B C E Q (dgParameterPullback A a τ) =
      dgParameterPullback A a (BimoduleTensor.firstParam A B C E Q τ) := by
  apply GradedNatTrans.ext
  funext e
  apply moduleHom_ext
  intro b
  change Bimodule.paramValue A B E
      (BimoduleTensor.firstParam A B C E Q (dgParameterPullback A a τ)) b e =
    (a ≫ (BimoduleTensor.firstParam A B C E Q τ).app e) ≫ _
  rw [BimoduleTensor.firstParam_value, Category.assoc, dgFirstParamHom_pullback]
  exact congrArg (fun k => a ≫ k) (BimoduleTensor.firstParam_value A B C E Q τ b e).symm

end SerrePositivity.KST.SConstruction
