module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleAssociatorPrecomp
/-!
概要：双加群射の実作用と逆結合子の自然性を、同じ全関手射で照合する。
方針：元の閉零成分・全 Hom 自然な厳密変換・同じ実 nerve を使う。
規約：原 Hom の平坦性と入力圏の Small 性を追加しない。
使われ方：元の通常合成比較 α の自然性と左単位三角式。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (E F : Type v) (C : Type (max (u + 1) v))
  [DGCategory R E] [Small.{u} E] [DGCategory R F] [Small.{u} F] [DGCategory R C]
/-- 同じ composeMap の閉零成分は、元の kernel 射の成分への入力評価に一致。 -/
lemma dgKernelBimoduleMap_precomp_closed {P Q : BimoduleCategory R F E}
    (η : P ⟶ Q) (H : DGFunctor R C (RightModule R E)) (x : C) :
    (BimoduleCategory.evaluation R F C x).map
      (BimoduleTensor.composeMap R F E C η (𝟙 (BimoduleCategory.of R E C H))) =
    (BimoduleCategory.evaluation R F (RightModule R E) (H.obj x)).map
      (BimoduleTensor.composeMap R F E (RightModule R E) η
        (𝟙 (BimoduleCategory.of R E (RightModule R E) (DGFunctor.id (RightModule R E))))) := by
  apply moduleMorphism_ext
  intro f
  change (BimoduleCategory.valueEvaluation R F C f x).map
      (BimoduleTensor.composeMap R F E C η (𝟙 (BimoduleCategory.of R E C H))) =
    (BimoduleCategory.valueEvaluation R F (RightModule R E) f (H.obj x)).map
      (BimoduleTensor.composeMap R F E (RightModule R E) η
        (𝟙 (BimoduleCategory.of R E (RightModule R E) (DGFunctor.id (RightModule R E)))))
  rw [BimoduleTensor.composeMap_value_eval, BimoduleTensor.composeMap_value_eval]
  simp only [BimoduleTensor.composeValueMap, CategoryTheory.Functor.map_id]
  rfl
/-- 同じ kernel 射の厳密変換は、任意の加群値 dg 関手による前合成に一致。 -/
lemma dgKernelBimoduleMap_precomp_strict_heq {P Q : BimoduleCategory R F E}
    (η : P ⟶ Q) (H : DGFunctor R C (RightModule R E)) :
    HEq (dgBimoduleMapStrictNatTrans R F C
      (BimoduleTensor.composeMap R F E C η (𝟙 (BimoduleCategory.of R E C H))))
      (dgStrictNatTransPrecomp H (dgBimoduleMapStrictNatTrans R F (RightModule R E)
        (BimoduleTensor.composeMap R F E (RightModule R E) η
          (𝟙 (BimoduleCategory.of R E (RightModule R E) (DGFunctor.id (RightModule R E))))))) := by
  have hf := (dgKernelTensor_postcomp_bimodule_eq R E F C H
    (BimoduleCategory.underlying R F E P)).symm
  have hg := (dgKernelTensor_postcomp_bimodule_eq R E F C H
    (BimoduleCategory.underlying R F E Q)).symm
  apply dgStrictNatTrans_heq_of_functor_eq _ _ hf hg
  intro x
  apply heq_of_eq
  change cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      ((BimoduleCategory.evaluation R F C x).map
        (BimoduleTensor.composeMap R F E C η (𝟙 (BimoduleCategory.of R E C H))))) =
    cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      ((BimoduleCategory.evaluation R F (RightModule R E) (H.obj x)).map
        (BimoduleTensor.composeMap R F E (RightModule R E) η
          (𝟙 (BimoduleCategory.of R E (RightModule R E) (DGFunctor.id (RightModule R E)))))))
  rw [dgKernelBimoduleMap_precomp_closed R E F C η H x]
  rfl
/-- 同じ kernel 射の全 nerve 変換は、任意の入力 dg 関手の実前合成に一致。 -/
lemma dgKernelBimoduleMap_precomp_nerve_hom_heq {P Q : BimoduleCategory R F E}
    (η : P ⟶ Q) (H : DGFunctor R C (RightModule R E)) :
    HEq ((dgBimoduleFunctorHomFunctor R F C).map
      (BimoduleTensor.composeMap R F E C η (𝟙 (BimoduleCategory.of R E C H))))
      ((SSet.mapHomotopyCategory ((pre (dgNerve.map H)).app (dgModuleNerve R F))).map
        ((dgBimoduleFunctorHomFunctor R F (RightModule R E)).map
          (BimoduleTensor.composeMap R F E (RightModule R E) η
            (𝟙 (BimoduleCategory.of R E (RightModule R E)
              (DGFunctor.id (RightModule R E))))))) := by
  have hf := (dgKernelTensor_postcomp_bimodule_eq R E F C H
    (BimoduleCategory.underlying R F E P)).symm
  have hg := (dgKernelTensor_postcomp_bimodule_eq R E F C H
    (BimoduleCategory.underlying R F E Q)).symm
  have hh := dgStrictNatTransNerveHom_heq_of_functor_eq _ _ hf hg
    (dgKernelBimoduleMap_precomp_strict_heq R E F C η H)
  exact hh.trans (dgStrictNatTransNerveHom_precomp_heq R C (RightModule R E) (RightModule R F)
    H (dgBimoduleMapStrictNatTrans R F (RightModule R E)
      (BimoduleTensor.composeMap R F E (RightModule R E) η
        (𝟙 (BimoduleCategory.of R E (RightModule R E) (DGFunctor.id (RightModule R E)))))))
end
end SerrePositivity.InfinityCategories
