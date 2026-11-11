module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleOutputComparisonRawSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionPrecompWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLiftNervePrecomposition
/-!
概要：元の resolved 前合成比較の実包含後の指定値を、同じ実入力比較へ同定する。
方針：元の入力 Up と半自由出力 Down の比較を保持して前後合成を交換する。
規約：元の指定比較を変更しない。使われ方：resolved augmentation 正方形への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
variable (A : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C)
/-- 元の resolved 比較の実包含後の値は、同じ入力比較の Up 制限と始点への後合成。 -/
lemma dgModuleResolvedInfinity_precompIso_rawSource_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A C E H F).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E))))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompSourceIso R A C E H F).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A))).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F))) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)
  let S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F)
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
    (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
  let RA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift R A E (H.comp F))
  let RC := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift R C E F)
  let UA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A)
  let UC := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))
  let I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E))
  let T := D ≫ I
  let O := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso R A C E H F
  let U := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R A C E H F
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompSourceIso R A C E H F
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)
  have h1 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq (U.postcomp D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A C E H F) rfl rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso_heq R A C E H F) I
  have h2 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp U D I)
  have hUp : UA ≫ h = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ UC :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLift_sourcePrecomp_nerve.{u, v, v} R A C H
  have ht : UA ≫ h ≫ S.inv ≫ RC = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ UC ≫ S.inv ≫ RC := by
    simpa only [Category.assoc] using congrArg (fun m => m ≫ S.inv ≫ RC) hUp
  have h3 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq (O.precomp UA) U rfl ht
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso_heq.{u, v, v} R A C E H F) T
  have h4 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp O UA T)
  have hr : J ≫ RC = RA := by
    have hr := congrArg (fun G => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor_replacementLift R A C E H F)
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using! hr
  have hRaw : RC ≫ T = r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift_rawSource R C E F
  have hf : (Q.inv ≫ J) ≫ r = (Q.inv ≫ RA) ≫ T := by
    calc
      _ = Q.inv ≫ J ≫ (RC ≫ T) := by rw [hRaw, Category.assoc]
      _ = (Q.inv ≫ (J ≫ RC)) ≫ T := by simp only [Category.assoc]
      _ = _ := by rw [hr]
  have hg : (h ≫ S.inv) ≫ r = (h ≫ S.inv ≫ RC) ≫ T := by
    calc
      _ = (h ≫ S.inv) ≫ (RC ≫ T) := congrArg (fun m => (h ≫ S.inv) ≫ m) hRaw.symm
      _ = _ := by simp only [Category.assoc]
  have h5 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq (e.postcomp r) (O.postcomp T) hf hg
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso_rawSource_heq R C E F A H) UA
  have h6 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp e UA r).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
