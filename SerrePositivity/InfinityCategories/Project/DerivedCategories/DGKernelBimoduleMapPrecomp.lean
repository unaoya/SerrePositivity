module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleAssociatorPrecomp
/-!
概要：双加群射の実作用と逆結合子の自然性を、同じ全関手射で照合する。
方針：元の閉零成分・全 Hom 自然な厳密変換・同じ実 nerve を使う。
規約：原 Hom の平坦性と入力圏の Small 性を追加しない。
使われ方：元の通常合成比較 α の自然性と左単位三角式。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (E F : Type v) (C : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ composeMap の閉零成分は、元の kernel 射の成分への入力評価に一致。 -/
lemma dgKernelBimoduleMap_precomp_closed {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E}
    (η : P ⟶ Q) (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) (x : C) :
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R F C x).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E C η (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C H))) =
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R F (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (H.obj x)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) η
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext
  intro f
  change (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R F C f x).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E C η (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C H))) =
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R F (_root_.SerrePositivity.DifferentialGraded.RightModule R E) f (H.obj x)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) η
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))))
  rw [_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_value_eval, _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_value_eval]
  simp only [_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueMap, CategoryTheory.Functor.map_id]
  rfl
/-- 同じ kernel 射の厳密変換は、任意の加群値 dg 関手による前合成に一致。 -/
lemma dgKernelBimoduleMap_precomp_strict_heq {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E}
    (η : P ⟶ Q) (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R F C
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E C η (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C H))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R F (RightModule R E)
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) η
          (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))))) := by
  have hf := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R E F C H
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E P)).symm
  have hg := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R E F C H
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q)).symm
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_heq_of_functor_eq _ _ hf hg
  intro x
  apply heq_of_eq
  change _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R F C x).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E C η (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C H))))) =
    _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R F (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (H.obj x)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) η
          (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))))))
  rw [dgKernelBimoduleMap_precomp_closed R E F C η H x]
  rfl
/-- 同じ kernel 射の全 nerve 変換は、任意の入力 dg 関手の実前合成に一致。 -/
lemma dgKernelBimoduleMap_precomp_nerve_hom_heq {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E}
    (η : P ⟶ Q) (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F C).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E C η (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C H))))
      ((SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)).app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R F))).map
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F (RightModule R E)).map
          (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) η
            (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
              (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))))) := by
  have hf := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R E F C H
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E P)).symm
  have hg := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R E F C H
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q)).symm
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_heq_of_functor_eq _ _ hf hg
    (dgKernelBimoduleMap_precomp_strict_heq R E F C η H)
  exact hh.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_precomp_heq R C (RightModule R E) (RightModule R F)
    H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R F (RightModule R E)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) η
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))))))
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
