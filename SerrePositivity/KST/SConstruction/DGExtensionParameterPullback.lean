module
public import SerrePositivity.KST.SConstruction.BimoduleParameterPullback
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGParameter

/-! # 元の実延長とラベル付き Perf 作用のパラメータ引き戻し
概要：入力パラメータ複体の射は、graph・実加群・Perf・ラベル付き作用と可換である。
方針：元の第一 tensor 変数の引き戻しから、充満制限と実閉零共役を通して証明する。
規約：元の全次数成分を変更しない。使われ方：入力 Hom の作用と単体的パラメータ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  {K L : Complex A} {F G : DGFunctor A D E}
  (a : L ⟶ K) (τ : DGFunctorParamTrans A D E K F G)

omit [Small.{u} D] in
/-- 元の graph 作用は、パラメータ射による引き戻しと可換。 -/
lemma dgFunctorGraphParameter_pullback :
    dgFunctorGraphParameter A D E (dgParameterPullback A a τ) =
      dgParameterPullback A a (dgFunctorGraphParameter A D E τ) := by
  apply GradedNatTrans.ext
  funext d
  exact Category.assoc _ _ _

/-- 元の実加群延長の全次数作用は、同じパラメータ引き戻しと可換。 -/
lemma dgModuleExtensionParameter_pullback :
    dgModuleExtensionParameter A D E (dgParameterPullback A a τ) =
      dgParameterPullback A a (dgModuleExtensionParameter A D E τ) := by
  unfold dgModuleExtensionParameter
  rw [dgFunctorGraphParameter_pullback, dgFirstParam_pullback]

/-- 元の実 Perf 延長の作用も、全 Hom 成分を保ってパラメータ引き戻しと可換。 -/
lemma perfectDGExtensionParameter_pullback :
    perfectDGExtensionParameter A D E (dgParameterPullback A a τ) =
      dgParameterPullback A a (perfectDGExtensionParameter A D E τ) := by
  apply GradedNatTrans.ext
  funext M
  change (dgModuleExtensionParameter A D E (dgParameterPullback A a τ)).app M.val =
    a ≫ (dgModuleExtensionParameter A D E τ).app M.val
  rw [dgModuleExtensionParameter_pullback]
  rfl

/-- ラベル付き Perf 作用への全パラメータ自然変換は、パラメータ引き戻しと可換。 -/
lemma presentedPerfectDGParameter_pullback :
    presentedPerfectDGParameter A D E (dgParameterPullback A a τ) =
      dgParameterPullback A a (presentedPerfectDGParameter A D E τ) := by
  apply GradedNatTrans.ext
  funext X
  simp only [presentedPerfectDGParameter_app, perfectDGExtensionParameter_pullback,
    dgParameterPullback_app]
  exact Category.assoc _ _ _

end SerrePositivity.KST.SConstruction
