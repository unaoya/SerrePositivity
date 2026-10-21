module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputComparisonRawSource
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompWhisker
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLiftNervePrecomposition
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
variable (A : Type (max (u + 1) v)) [DGCategory R A] (H : DGFunctor R A C)
/-- 元の resolved 比較の実包含後の値は、同じ入力比較の Up 制限と始点への後合成。 -/
lemma dgModuleResolvedInfinity_precompIso_rawSource_heq :
    HEq ((dgModuleResolvedInfinity_precompIso R A C E H F).postcomp
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E))))
      (((dgModuleResolutionPrecompSourceIso R A C E H F).precomp
        (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A))).postcomp
        (dgNerve.map (dgModuleAugmentationSource R C E F))) := by
  let Q := dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)
  let S := dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let J := dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F)
  let h := dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
    (H.comp (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
  let RA := dgNerve.map (dgModuleFunctorResolutionReplacementLift R A E (H.comp F))
  let RC := dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F)
  let UA := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A)
  let UC := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)
  let D := dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
    (SemifreeDGModules R E))
  let I := dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
    (dgModuleSemifreeProperty R E))
  let T := D ≫ I
  let O := dgModuleOutputResolution_precompIso R A C E H F
  let U := dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R A C E H F
  let e := dgModuleResolutionPrecompSourceIso R A C E H F
  let r := dgNerve.map (dgModuleAugmentationSource R C E F)
  have h1 := F2.functorIso_postcomp_heq_of_heq (U.postcomp D)
    (dgModuleResolvedInfinity_precompIso R A C E H F) rfl rfl
    (dgModuleResolvedInfinity_precompIso_heq R A C E H F) I
  have h2 := heq_of_eq (F2.functorIso_postcomp_postcomp U D I)
  have hUp : UA ≫ h = dgNerve.map H ≫ UC :=
    dgUniverseLift_sourcePrecomp_nerve.{u, v, v} R A C H
  have ht : UA ≫ h ≫ S.inv ≫ RC = dgNerve.map H ≫ UC ≫ S.inv ≫ RC := by
    simpa only [Category.assoc] using congrArg (fun m => m ≫ S.inv ≫ RC) hUp
  have h3 := F2.functorIso_postcomp_heq_of_heq (O.precomp UA) U rfl ht
    (dgModuleOutputResolution_unliftedPrecompIso_heq.{u, v, v} R A C E H F) T
  have h4 := heq_of_eq (F2.functorIso_precomp_postcomp O UA T)
  have hr : J ≫ RC = RA := by
    have hr := congrArg (fun G => dgNerve.map G)
      (dgModuleResolutionPrecompFunctor_replacementLift R A C E H F)
    simpa only [dgNerve.map_comp] using! hr
  have hRaw : RC ≫ T = r := dgModuleFunctorResolutionReplacementLift_rawSource R C E F
  have hf : (Q.inv ≫ J) ≫ r = (Q.inv ≫ RA) ≫ T := by
    calc
      _ = Q.inv ≫ J ≫ (RC ≫ T) := by rw [hRaw, Category.assoc]
      _ = (Q.inv ≫ (J ≫ RC)) ≫ T := by simp only [Category.assoc]
      _ = _ := by rw [hr]
  have hg : (h ≫ S.inv) ≫ r = (h ≫ S.inv ≫ RC) ≫ T := by
    calc
      _ = (h ≫ S.inv) ≫ (RC ≫ T) := congrArg (fun m => (h ≫ S.inv) ≫ m) hRaw.symm
      _ = _ := by simp only [Category.assoc]
  have h5 := F2.functorIso_precomp_heq_of_heq (e.postcomp r) (O.postcomp T) hf hg
    (dgModuleOutputResolution_precompIso_rawSource_heq R C E F A H) UA
  have h6 := heq_of_eq (F2.functorIso_precomp_postcomp e UA r).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
end SerrePositivity.InfinityCategories
