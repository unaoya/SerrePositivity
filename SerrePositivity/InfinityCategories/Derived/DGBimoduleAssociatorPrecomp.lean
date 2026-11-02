module
public import SerrePositivity.InfinityCategories.Derived.DGKernelPostcompBimodule
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (E F : Type v)
  (C B : Type (max (u + 1) v))
  [DGCategory R E] [Small.{u} E] [DGCategory R F] [Small.{u} F]
  [DGCategory R C] [DGCategory R B]
/-- 入力 dg 関手による制限と同じ通常双加群合成は、dg 関手として厳密に一致。 -/
lemma dgKernelTensor_precomp_bimodule_eq (H : DGFunctor R B C)
    (P : Bimodule R E C) (Q : Bimodule R F E) :
    H.comp (BimoduleTensor.compose R F E C Q P).toFunctor =
      (BimoduleTensor.compose R F E B Q (H.comp P.toFunctor)).toFunctor := by
  rw [← dgKernelTensor_postcomp_bimodule_eq R E F C P Q,
    ← dgKernelTensor_postcomp_bimodule_eq R E F B (H.comp P.toFunctor) Q]
  apply EnrichedFunctor.ext (Complex R)
    (F := H.comp (P.toFunctor.comp (Morita.kernelTensor R E F Q)))
    (G := (H.comp P.toFunctor).comp (Morita.kernelTensor R E F Q)) (fun _ => rfl)
  intro x y
  change (H.map x y ≫ (P.toFunctor.map _ _ ≫ (Morita.kernelTensor R E F Q).map _ _)) ≫
    𝟙 _ = (H.map x y ≫ P.toFunctor.map _ _) ≫ (Morita.kernelTensor R E F Q).map _ _
  rw [Category.comp_id, Category.assoc]
variable (G : Type v) [DGCategory R G] [Small.{u} G]
/-- 同じ結合子の閉零成分は、入力 dg 関手で評価しても変わらない。 -/
lemma dgBimoduleAssociator_precomp_closed_hom (H : DGFunctor R B C)
    (P : Bimodule R G F) (Q : Bimodule R F E) (T : Bimodule R E C) (x : B) :
    (BimoduleCategory.evaluation R G B x).map
      (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom =
    (BimoduleCategory.evaluation R G C (H.obj x)).map
      (BimoduleTensor.associatorIso R G F E C P Q T).hom := by
  apply moduleMorphism_ext
  intro g
  change (BimoduleCategory.valueEvaluation R G B g x).map
      (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom =
    (BimoduleCategory.valueEvaluation R G C g (H.obj x)).map
      (BimoduleTensor.associatorIso R G F E C P Q T).hom
  rw [BimoduleTensor.associatorIso_hom_value_eval, BimoduleTensor.associatorIso_hom_value_eval]
  unfold BimoduleTensor.associatorValueIso
  rfl
/-- 同じ逆結合子の閉零成分は、入力 dg 関手で評価しても変わらない。 -/
lemma dgBimoduleAssociator_precomp_closed_inv (H : DGFunctor R B C)
    (P : Bimodule R G F) (Q : Bimodule R F E) (T : Bimodule R E C) (x : B) :
    (BimoduleCategory.evaluation R G B x).map
      (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv =
    (BimoduleCategory.evaluation R G C (H.obj x)).map
      (BimoduleTensor.associatorIso R G F E C P Q T).inv := by
  apply moduleMorphism_ext
  intro g
  change (BimoduleCategory.valueEvaluation R G B g x).map
      (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv =
    (BimoduleCategory.valueEvaluation R G C g (H.obj x)).map
      (BimoduleTensor.associatorIso R G F E C P Q T).inv
  rw [BimoduleTensor.associatorIso_inv_value_eval, BimoduleTensor.associatorIso_inv_value_eval]
  unfold BimoduleTensor.associatorValueIso
  rfl
/-- 同じ結合子の厳密変換は、入力 dg 関手による前合成に一致。 -/
lemma dgBimoduleAssociator_precomp_strict_hom_heq (H : DGFunctor R B C)
    (P : Bimodule R G F) (Q : Bimodule R F E) (T : Bimodule R E C) :
    HEq (dgBimoduleMapStrictNatTrans R G B
      (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom)
      (dgStrictNatTransPrecomp H (dgBimoduleMapStrictNatTrans R G C
        (BimoduleTensor.associatorIso R G F E C P Q T).hom)) := by
  have hf := (dgKernelTensor_precomp_bimodule_eq R E G C B H T
    (BimoduleTensor.compose R G F E P Q)).symm
  have hg : (BimoduleTensor.compose R G F B P
      (BimoduleTensor.compose R F E B Q (H.comp T.toFunctor))).toFunctor =
      H.comp (BimoduleTensor.compose R G F C P
        (BimoduleTensor.compose R F E C Q T)).toFunctor := by
    rw [dgKernelTensor_precomp_bimodule_eq R F G C B H (BimoduleTensor.compose R F E C Q T) P,
      dgKernelTensor_precomp_bimodule_eq R E F C B H T Q]
  apply dgStrictNatTrans_heq_of_functor_eq _ _ hf hg
  intro x
  apply heq_of_eq
  change cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      ((BimoduleCategory.evaluation R G B x).map
        (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom)) =
    cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      ((BimoduleCategory.evaluation R G C (H.obj x)).map
        (BimoduleTensor.associatorIso R G F E C P Q T).hom))
  rw [dgBimoduleAssociator_precomp_closed_hom R E F C B G H P Q T x]
  rfl

/-- 同じ逆結合子の厳密変換は、入力 dg 関手による前合成に一致。 -/
lemma dgBimoduleAssociator_precomp_strict_inv_heq (H : DGFunctor R B C)
    (P : Bimodule R G F) (Q : Bimodule R F E) (T : Bimodule R E C) :
    HEq (dgBimoduleMapStrictNatTrans R G B
      (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv)
      (dgStrictNatTransPrecomp H (dgBimoduleMapStrictNatTrans R G C
        (BimoduleTensor.associatorIso R G F E C P Q T).inv)) := by
  have hf := (dgKernelTensor_precomp_bimodule_eq R E G C B H T
    (BimoduleTensor.compose R G F E P Q)).symm
  have hg : (BimoduleTensor.compose R G F B P
      (BimoduleTensor.compose R F E B Q (H.comp T.toFunctor))).toFunctor =
      H.comp (BimoduleTensor.compose R G F C P
        (BimoduleTensor.compose R F E C Q T)).toFunctor := by
    rw [dgKernelTensor_precomp_bimodule_eq R F G C B H (BimoduleTensor.compose R F E C Q T) P,
      dgKernelTensor_precomp_bimodule_eq R E F C B H T Q]
  apply dgStrictNatTrans_heq_of_functor_eq _ _ hg hf
  intro x
  apply heq_of_eq
  change cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      ((BimoduleCategory.evaluation R G B x).map
        (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv)) =
    cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      ((BimoduleCategory.evaluation R G C (H.obj x)).map
        (BimoduleTensor.associatorIso R G F E C P Q T).inv))
  rw [dgBimoduleAssociator_precomp_closed_inv R E F C B G H P Q T x]
  rfl


/-- 同じ結合子の nerve 像は、元の全関手射の前合成に一致。 -/
lemma dgBimoduleAssociator_precomp_nerve_hom_heq (H : DGFunctor R B C)
    (P : Bimodule R G F) (Q : Bimodule R F E) (T : Bimodule R E C) :
    HEq ((dgBimoduleFunctorHomFunctor R G B).map
      (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom)
      ((SSet.mapHomotopyCategory ((pre (dgNerve.map H)).app (dgModuleNerve R G))).map
        ((dgBimoduleFunctorHomFunctor R G C).map
          (BimoduleTensor.associatorIso R G F E C P Q T).hom)) := by
  have hf := (dgKernelTensor_precomp_bimodule_eq R E G C B H T
    (BimoduleTensor.compose R G F E P Q)).symm
  have hg : (BimoduleTensor.compose R G F B P
      (BimoduleTensor.compose R F E B Q (H.comp T.toFunctor))).toFunctor =
      H.comp (BimoduleTensor.compose R G F C P
        (BimoduleTensor.compose R F E C Q T)).toFunctor := by
    rw [dgKernelTensor_precomp_bimodule_eq R F G C B H (BimoduleTensor.compose R F E C Q T) P,
      dgKernelTensor_precomp_bimodule_eq R E F C B H T Q]
  have hh := dgStrictNatTransNerveHom_heq_of_functor_eq
    (dgBimoduleMapStrictNatTrans R G B
      (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).hom)
    (dgStrictNatTransPrecomp H (dgBimoduleMapStrictNatTrans R G C
      (BimoduleTensor.associatorIso R G F E C P Q T).hom)) hf hg
    (dgBimoduleAssociator_precomp_strict_hom_heq R E F C B G H P Q T)
  exact hh.trans (dgStrictNatTransNerveHom_precomp_heq R B C (RightModule R G) H
    (dgBimoduleMapStrictNatTrans R G C (BimoduleTensor.associatorIso R G F E C P Q T).hom))
/-- 同じ逆結合子の nerve 像は、元の全関手射の前合成に一致。 -/
lemma dgBimoduleAssociator_precomp_nerve_inv_heq (H : DGFunctor R B C)
    (P : Bimodule R G F) (Q : Bimodule R F E) (T : Bimodule R E C) :
    HEq ((dgBimoduleFunctorHomFunctor R G B).map
      (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv)
      ((SSet.mapHomotopyCategory ((pre (dgNerve.map H)).app (dgModuleNerve R G))).map
        ((dgBimoduleFunctorHomFunctor R G C).map
          (BimoduleTensor.associatorIso R G F E C P Q T).inv)) := by
  have hf := (dgKernelTensor_precomp_bimodule_eq R E G C B H T
    (BimoduleTensor.compose R G F E P Q)).symm
  have hg : (BimoduleTensor.compose R G F B P
      (BimoduleTensor.compose R F E B Q (H.comp T.toFunctor))).toFunctor =
      H.comp (BimoduleTensor.compose R G F C P
        (BimoduleTensor.compose R F E C Q T)).toFunctor := by
    rw [dgKernelTensor_precomp_bimodule_eq R F G C B H (BimoduleTensor.compose R F E C Q T) P,
      dgKernelTensor_precomp_bimodule_eq R E F C B H T Q]
  have hh := dgStrictNatTransNerveHom_heq_of_functor_eq
    (dgBimoduleMapStrictNatTrans R G B
      (BimoduleTensor.associatorIso R G F E B P Q (H.comp T.toFunctor)).inv)
    (dgStrictNatTransPrecomp H (dgBimoduleMapStrictNatTrans R G C
      (BimoduleTensor.associatorIso R G F E C P Q T).inv)) hg hf
    (dgBimoduleAssociator_precomp_strict_inv_heq R E F C B G H P Q T)
  exact hh.trans (dgStrictNatTransNerveHom_precomp_heq R B C (RightModule R G) H
    (dgBimoduleMapStrictNatTrans R G C (BimoduleTensor.associatorIso R G F E C P Q T).inv))
end SerrePositivity.InfinityCategories
