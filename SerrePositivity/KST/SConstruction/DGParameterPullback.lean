module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomUniversal

/-! # パラメータ複体の射による全次数自然変換の引き戻し
概要：K′→K に沿ってパラメータを引き戻し、元の成分と全 Hom 自然性を保持する。
方針：既存の豊穣自然変換の前層を用いる。
規約：始域の smallness や end の存在を要求しない。使われ方：高次入力の面・退化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E] {F G : DGFunctor A D E}

/-- 元の任意パラメータ付き自然変換の、パラメータ射に沿う引き戻し。 -/
def dgParameterPullback {K L : Complex A} (a : L ⟶ K)
    (τ : DGFunctorParamTrans A D E K F G) : DGFunctorParamTrans A D E L F G :=
  (enrichedNatTransYoneda F G).map a.op τ

/-- 引き戻しは、全対象の同じ元の成分への前合成。 -/
lemma dgParameterPullback_app {K L : Complex A} (a : L ⟶ K)
    (τ : DGFunctorParamTrans A D E K F G) (x : D) :
    (dgParameterPullback A a τ).app x = a ≫ τ.app x := rfl

/-- 恒等パラメータ射に沿う引き戻しは恒等。 -/
lemma dgParameterPullback_id {K : Complex A} (τ : DGFunctorParamTrans A D E K F G) :
    dgParameterPullback A (𝟙 K) τ = τ := by
  apply GradedNatTrans.ext
  funext x
  exact Category.id_comp _

/-- パラメータ射の合成に沿う引き戻しは、連続した引き戻しと一致する。 -/
lemma dgParameterPullback_comp {K L J : Complex A} (a : L ⟶ K) (b : J ⟶ L)
    (τ : DGFunctorParamTrans A D E K F G) :
    dgParameterPullback A (b ≫ a) τ = dgParameterPullback A b (dgParameterPullback A a τ) := by
  apply GradedNatTrans.ext
  funext x
  exact Category.assoc _ _ _

end SerrePositivity.KST.SConstruction
