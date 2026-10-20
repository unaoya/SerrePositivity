module
public import SerrePositivity.KST.SConstruction.BimoduleParameterUnit
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGParameter

/-! # graph・実延長・ラベル付き作用の高次単位保存
概要：元の入力の単位自然変換は、各段で同じ元の単位を回収する。
方針：dg Yoneda と tensor の単位保存を、Perf の充満制限と実閉零共役へ通す。
規約：零単体の関手法則と区別する。使われ方：元の入力 Hom 作用の閉単位保存。
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
  (F : DGFunctor A D E)

omit [Small.{u} D] in
/-- 元の入力の単位自然変換は、graph の全 Hom の単位自然変換となる。 -/
lemma dgFunctorGraphParameter_identity :
    dgFunctorGraphParameter A D E (dgFunctorParamIdentity A D E F) =
      dgFunctorParamIdentity A D (RightModule A E) (functorGraph A D E F).toFunctor := by
  apply GradedNatTrans.ext
  funext d
  exact (dgYoneda A E).map_id (F.obj d)

/-- 元の実加群延長は、入力の単位自然変換を同じ単位自然変換へ送る。 -/
lemma dgModuleExtensionParameter_identity :
    dgModuleExtensionParameter A D E (dgFunctorParamIdentity A D E F) =
      dgFunctorParamIdentity A (RightModule A D) (RightModule A E) (dgModuleExtension A D E F) := by
  unfold dgModuleExtensionParameter
  rw [dgFunctorGraphParameter_identity, dgFirstParam_identity]
  rfl

/-- 元の実 Perf 延長の全パラメータ作用も、単位自然変換を保持する。 -/
lemma perfectDGExtensionParameter_identity :
    perfectDGExtensionParameter A D E (dgFunctorParamIdentity A D E F) =
      dgFunctorParamIdentity A (PerfectDGModule A D) (PerfectDGModule A E)
        (perfectDGExtension A D E F) := by
  apply GradedNatTrans.ext
  funext M
  change (dgModuleExtensionParameter A D E (dgFunctorParamIdentity A D E F)).app M.val = _
  rw [dgModuleExtensionParameter_identity]
  rfl

/-- ラベル付き dg 作用は、元の入力の単位自然変換を元の単位へ送る。 -/
lemma presentedPerfectDGParameter_identity :
    presentedPerfectDGParameter A D E (dgFunctorParamIdentity A D E F) =
      dgFunctorParamIdentity A (PresentedPerfectDGObject A D) (PresentedPerfectDGObject A E)
        (presentedPerfectDGAction A D E F) := by
  apply GradedNatTrans.ext
  funext X
  rw [presentedPerfectDGParameter_app, perfectDGExtensionParameter_identity]
  exact enrichedClosedIsoConjugation_id (Complex A) (presentedPerfectDGActionIso A D E F X)

end SerrePositivity.KST.SConstruction
