module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelPostcompBimodule
public import SerrePositivity.DifferentialGraded.Tensor.Triple
/-!
概要：元の通常双加群結合子とその逆を、入力 dg 関手の制限と実 nerve で照合する。
方針：同じ dg 関手の端点等式と、全 Hom 自然な閉零成分の評価式を使う。
規約：入力圏の Small 性は不要。使われ方：kernel の triangle・pentagon の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (E F : Type v)
  (C B : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B]
/-- 入力 dg 関手による制限と同じ通常双加群合成は、dg 関手として厳密に一致。 -/
lemma dgKernelTensor_precomp_bimodule_eq (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C)
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E C) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) :
    H.comp (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q P).toFunctor =
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E B Q (H.comp P.toFunctor)).toFunctor := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R E F C P Q,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensor_postcomp_bimodule_eq R E F B (H.comp P.toFunctor) Q]
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := H.comp (P.toFunctor.comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F Q)))
    (G := (H.comp P.toFunctor).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F Q)) (fun _ => rfl)
  intro x y
  change (H.map x y ≫ (P.toFunctor.map _ _ ≫ (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F Q).map _ _)) ≫
    𝟙 _ = (H.map x y ≫ P.toFunctor.map _ _) ≫ (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F Q).map _ _
  rw [Category.comp_id, Category.assoc]
variable (G : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R G] [Small.{u} G]
/-- 同じ結合子の閉零成分は、入力 dg 関手で評価しても変わらない。 -/
lemma dgBimoduleAssociator_precomp_closed_hom (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C)
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (T : _root_.SerrePositivity.DifferentialGraded.Bimodule R E C) (x : B) :
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R G B x).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom =
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R G C (H.obj x)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).hom := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext
  intro g
  change (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R G B g x).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom =
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R G C g (H.obj x)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).hom
  rw [_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_hom_value_eval, _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_hom_value_eval]
  unfold _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueIso
  rfl
/-- 同じ逆結合子の閉零成分は、入力 dg 関手で評価しても変わらない。 -/
lemma dgBimoduleAssociator_precomp_closed_inv (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C)
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (T : _root_.SerrePositivity.DifferentialGraded.Bimodule R E C) (x : B) :
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R G B x).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv =
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R G C (H.obj x)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).inv := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext
  intro g
  change (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R G B g x).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv =
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R G C g (H.obj x)).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).inv
  rw [_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_inv_value_eval, _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_inv_value_eval]
  unfold _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueIso
  rfl
/-- 同じ結合子の厳密変換は、入力 dg 関手による前合成に一致。 -/
lemma dgBimoduleAssociator_precomp_strict_hom_heq (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C)
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (T : _root_.SerrePositivity.DifferentialGraded.Bimodule R E C) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R G B
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R G C
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).hom)) := by
  have hf := (dgKernelTensor_precomp_bimodule_eq R E G C B H T
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F E P Q)).symm
  have hg : (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F B P
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E B Q (H.comp T.toFunctor))).toFunctor =
      H.comp (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F C P
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q T)).toFunctor := by
    rw [dgKernelTensor_precomp_bimodule_eq R F G C B H (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q T) P,
      dgKernelTensor_precomp_bimodule_eq R E F C B H T Q]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_heq_of_functor_eq _ _ hf hg
  intro x
  apply heq_of_eq
  change _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R G B x).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom)) =
    _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R G C (H.obj x)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).hom))
  rw [dgBimoduleAssociator_precomp_closed_hom R E F C B G H P Q T x]
  rfl

/-- 同じ逆結合子の厳密変換は、入力 dg 関手による前合成に一致。 -/
lemma dgBimoduleAssociator_precomp_strict_inv_heq (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C)
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (T : _root_.SerrePositivity.DifferentialGraded.Bimodule R E C) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R G B
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R G C
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).inv)) := by
  have hf := (dgKernelTensor_precomp_bimodule_eq R E G C B H T
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F E P Q)).symm
  have hg : (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F B P
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E B Q (H.comp T.toFunctor))).toFunctor =
      H.comp (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F C P
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q T)).toFunctor := by
    rw [dgKernelTensor_precomp_bimodule_eq R F G C B H (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q T) P,
      dgKernelTensor_precomp_bimodule_eq R E F C B H T Q]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_heq_of_functor_eq _ _ hg hf
  intro x
  apply heq_of_eq
  change _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R G B x).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv)) =
    _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R G C (H.obj x)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).inv))
  rw [dgBimoduleAssociator_precomp_closed_inv R E F C B G H P Q T x]
  rfl


/-- 同じ結合子の nerve 像は、元の全関手射の前合成に一致。 -/
lemma dgBimoduleAssociator_precomp_nerve_hom_heq (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C)
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (T : _root_.SerrePositivity.DifferentialGraded.Bimodule R E C) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R G B).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom)
      ((SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)).app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R G))).map
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R G C).map
          (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).hom)) := by
  have hf := (dgKernelTensor_precomp_bimodule_eq R E G C B H T
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F E P Q)).symm
  have hg : (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F B P
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E B Q (H.comp T.toFunctor))).toFunctor =
      H.comp (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F C P
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q T)).toFunctor := by
    rw [dgKernelTensor_precomp_bimodule_eq R F G C B H (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q T) P,
      dgKernelTensor_precomp_bimodule_eq R E F C B H T Q]
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_heq_of_functor_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R G B
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R G C
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).hom)) hf hg
    (dgBimoduleAssociator_precomp_strict_hom_heq R E F C B G H P Q T)
  exact hh.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_precomp_heq R B C (RightModule R G) H
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R G C (BimoduleTensor.associatorIso R G F E C P Q T).hom))
/-- 同じ逆結合子の nerve 像は、元の全関手射の前合成に一致。 -/
lemma dgBimoduleAssociator_precomp_nerve_inv_heq (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C)
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R G F) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) (T : _root_.SerrePositivity.DifferentialGraded.Bimodule R E C) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R G B).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv)
      ((SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)).app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R G))).map
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R G C).map
          (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).inv)) := by
  have hf := (dgKernelTensor_precomp_bimodule_eq R E G C B H T
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F E P Q)).symm
  have hg : (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F B P
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E B Q (H.comp T.toFunctor))).toFunctor =
      H.comp (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R G F C P
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q T)).toFunctor := by
    rw [dgKernelTensor_precomp_bimodule_eq R F G C B H (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q T) P,
      dgKernelTensor_precomp_bimodule_eq R E F C B H T Q]
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_heq_of_functor_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R G B
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R G C
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R G F E C P Q T).inv)) hg hf
    (dgBimoduleAssociator_precomp_strict_inv_heq R E F C B G H P Q T)
  exact hh.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_precomp_heq R B C (RightModule R G) H
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R G C (BimoduleTensor.associatorIso R G F E C P Q T).inv))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
