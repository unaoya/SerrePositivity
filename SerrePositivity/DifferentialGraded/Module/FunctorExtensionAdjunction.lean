module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionUnitNaturality
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionCounitNaturality

/-! # graph tensor延長とdg関手に沿う制限の随伴

## 概要
graph tensor延長とdg関手に沿う制限の随伴。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgModule_right_triangle (M : ModuleCategory A E) :
    (dgModuleUnit A D E F).app ((moduleRestriction A D E F.op).obj M) ≫
      (moduleRestriction A D E F.op).map ((dgModuleCounit A D E F).app M) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro d
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  change (moduleEvaluation A D d).map (functorExtensionUnit A D E F
      (restrictModule A D E F.op (ForgetEnrichment.to (Complex A) M))) ≫
    (moduleEvaluation A D d).map ((moduleRestriction A D E F.op).map
      (functorExtensionCounit A D E F (ForgetEnrichment.to (Complex A) M))) = _
  rw [functorExtensionUnit_eval, moduleRestriction_map_eval, functorExtensionCounit_eval]
  exact functorExtensionInsertion_evaluation A D E F (ForgetEnrichment.to (Complex A) M) d

lemma dgModule_left_triangle (M : ModuleCategory A D) :
    (dgModuleExtension A D E F).onClosed.map ((dgModuleUnit A D E F).app M) ≫
      (dgModuleCounit A D E F).app ((dgModuleExtension A D E F).onClosed.obj M) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro e
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  change (moduleEvaluation A E e).map ((dgModuleExtension A D E F).onClosed.map
      (functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M))) ≫
    (moduleEvaluation A E e).map (functorExtensionCounit A D E F
      ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M))) = _
  rw [dgModuleExtension_map_eval, functorExtensionCounit_eval]
  apply Cochain.ofHom_injective
  apply BalancedTensor.cochain_zero_element_ext A D
    (ForgetEnrichment.to (Complex A) M) ((functorGraph A D E F).leftAt e)
  intro d r s n hn m h
  simp only [Cochain.ofHom_v]
  change (functorExtensionEvaluationComponent A D E F
      ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M)) e).f n
    ((BalancedTensor.rightTensorMap A D ((functorGraph A D E F).leftAt e)
      (functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M))).f n
      (BalancedTensor.element A D (ForgetEnrichment.to (Complex A) M)
        ((functorGraph A D E F).leftAt e) d m h hn)) =
    BalancedTensor.element A D (ForgetEnrichment.to (Complex A) M)
      ((functorGraph A D E F).leftAt e) d m h hn
  refine (congrArg (fun z => (functorExtensionEvaluationComponent A D E F
    ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M)) e).f n z)
    (BalancedTensor.rightTensorMap_element A D ((functorGraph A D E F).leftAt e)
      (functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M)) d m h hn)).trans ?_
  rw [functorExtensionUnit_eval]
  change (functorExtensionEvaluationComponent A D E F
      ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M)) e).f n
    (BalancedTensor.element A D
      (restrictModule A D E F.op
        ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M)))
      ((functorGraph A D E F).leftAt e) d
      ((functorExtensionInsertionComponent A D E F
        (ForgetEnrichment.to (Complex A) M) d).f r m) h hn) = _
  rw [functorExtensionInsertion_apply]
  rw [functorExtensionEvaluation_element,
    dgModuleExtension_action_element A D E F _ (op (F.obj d)) (op e) d
      (add_zero r) (zero_add s) hn, representable_action, unit_forward]
  simp only [smul_smul, mul_comm s r, Int.units_mul_self, one_smul]

/-- 任意のdg関手について、全dg加群の閉零射圏上でgraph延長は制限の左随伴。 -/
def dgModuleExtensionRestrictionAdjunction :
    (dgModuleExtension A D E F).onClosed ⊣ moduleRestriction A D E F.op :=
  Adjunction.mkOfUnitCounit {
    unit := dgModuleUnit A D E F
    counit := dgModuleCounit A D E F
    left_triangle := by
      apply NatTrans.ext
      funext M
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Category.id_comp, Category.comp_id,
        Functor.comp_obj, Functor.id_obj, NatTrans.id] using dgModule_left_triangle A D E F M
    right_triangle := by
      apply NatTrans.ext
      funext M
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id,
        Functor.comp_obj, Functor.id_obj, NatTrans.id] using dgModule_right_triangle A D E F M }

end SerrePositivity.DifferentialGraded
