module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionInputComparison
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationInputBaseHomotopy
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerComposition
/-!
概要：元の出力比較を同じ実 augmentation 始点上の入力比較へ移す。
方針：元の出力射影の下降・包含を厳密に計算し、指定値の後合成を移す。
規約：新しい比較を選ばない。使われ方：元の resolved 比較と実 augmentation の正方形。
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
/-- 実半自由出力射影の下降・包含は、元の augmentation 始点の nerve そのものである。 -/
lemma dgModuleFunctorResolutionReplacementLift_rawSource :
    dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (SemifreeDGModules R E)) ≫
      dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)) =
    dgNerve.map (dgModuleAugmentationSource R C E F) := by
  have hs := congrArg (fun J => dgNerve.map J)
    (dgUniverseLiftUp_comp_down.{u, max (u + 1) v, max (u + 1) v} R (SemifreeDGModules R E))
  simp only [dgNerve.map_comp, dgNerve.map_id] at hs
  simp only [dgModuleFunctorResolutionReplacementLift, dgModuleAugmentationSource,
    dgNerve.map_comp, Category.assoc]
  rw [← Category.assoc
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R
      (SemifreeDGModules R E))), hs, Category.id_comp]
variable (A : Type (max (u + 1) v)) [DGCategory R A] (H : DGFunctor R A C)
/-- 元の出力比較の下降・包含後の値は、同じ入力比較の augmentation 始点への後合成。 -/
lemma dgModuleOutputResolution_precompIso_rawSource_heq :
    HEq ((dgModuleOutputResolution_precompIso R A C E H F).postcomp
      (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (SemifreeDGModules R E)) ≫
      dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E))))
      ((dgModuleResolutionPrecompSourceIso R A C E H F).postcomp
        (dgNerve.map (dgModuleAugmentationSource R C E F))) := by
  let Q := dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)
  let S := dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let J := dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F)
  let h := dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
    (H.comp (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
  let RA := dgNerve.map (dgModuleFunctorResolutionReplacementLift R A E (H.comp F))
  let RC := dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F)
  let T := dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
    (SemifreeDGModules R E)) ≫
    dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E))
  let e := dgModuleResolutionPrecompSourceIso R A C E H F
  have hr : J ≫ RC = RA := by
    have hr := congrArg (fun G => dgNerve.map G)
      (dgModuleResolutionPrecompFunctor_replacementLift R A C E H F)
    simpa only [dgNerve.map_comp] using! hr
  have hf : (Q.inv ≫ J) ≫ RC = Q.inv ≫ RA := by rw [Category.assoc, hr]
  have hg : (h ≫ S.inv) ≫ RC = h ≫ S.inv ≫ RC := Category.assoc _ _ _
  have h1 := F2.functorIso_postcomp_heq_of_heq (e.postcomp RC)
    (dgModuleOutputResolution_precompIso R A C E H F) hf hg
    (dgModuleOutputResolution_precompIso_sourceComparison_heq R A C E H F) T
  have h2 := heq_of_eq (F2.functorIso_postcomp_postcomp e RC T)
  have h3 := F2.functorIso_postcomp_heq_of_map_eq e
    (dgModuleFunctorResolutionReplacementLift_rawSource R C E F)
  exact h1.trans (h2.trans h3)
end SerrePositivity.InfinityCategories
