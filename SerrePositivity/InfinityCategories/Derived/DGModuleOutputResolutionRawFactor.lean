module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedChangeRawValue
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeComparisonHom
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorNaturality
/-!
概要：元の指定 raw factor を、同じ入力切断と raw 出力射影の前合成比較へ回収する。
方針：出力の上げ下げ・同じ graph の入力前合成・指定比較の後合成を照合する。
規約：元の raw factor の値と全端点を保持。使われ方：分解変更の共役式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
def dgModuleOutputResolution_rawFactorPrecompIso :
    FunctorIso ((dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id
      (RightModule R E)))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R C E
      (F.comp (DGFunctor.id (RightModule R E)))))) ((dgNerve.map
      (dgModuleResolutionLiftedInputFunctor R C E F)) ≫
      (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E))))) :=
  qCatResolutionOutputPrecompIso (dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp
    (DGFunctor.id (RightModule R E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R
    (RightModule R E) E (DGFunctor.id (RightModule R E))) (dgNerve.map
    (dgModuleResolutionLiftedInputFunctor R C E F)) (dgNerve.map
    (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F (DGFunctor.id (RightModule R
    E)))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id
    (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule R
    E) E (DGFunctor.id (RightModule R E))))
    (dgModuleResolutionChangeIdentity_left_source_lift R C E F)
    (dgModuleResolutionChangeIdentity_left_output R C E F)
lemma dgModuleOutputResolution_precompIso_Id_down_heq :
    HEq ((dgModuleOutputResolution_precompIso R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E))).postcomp (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u +
      1) v} R (SemifreeDGModules R E)))) (dgModuleOutputResolution_rawFactorPrecompIso R C E F)
      := by
  have hS := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionPrecompFunctor_sourceLift R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E)))
  have hR := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionPrecompFunctor_replacementLift R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E)))
  simp only [dgNerve.map_comp] at hS hR
  unfold dgModuleOutputResolution_precompIso dgModuleOutputResolution_rawFactorPrecompIso
  exact qCatResolutionOutputPrecompIso_postcomp_heq_of_outputs
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id (RightModule R
      E)))) (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E
      (DGFunctor.id (RightModule R E))) (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C
      E F)) (dgNerve.map (dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)))) (dgNerve.map (dgModuleFunctorResolutionReplacementLift
      R C E (F.comp (DGFunctor.id (RightModule R E))))) (dgNerve.map
      (dgModuleFunctorResolutionReplacementLift R (RightModule R E) E (DGFunctor.id
      (RightModule R E)))) (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp
      (DGFunctor.id (RightModule R E))))) (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E)))) hS hR
    (dgModuleResolutionChangeIdentity_left_output R C E F) (dgNerve.map (dgUniverseLiftDown.{u,
      max (u + 1) v, max (u + 1) v} R (SemifreeDGModules R E)))
    (dgModuleFunctorResolutionReplacementLift_down R C E (F.comp (DGFunctor.id (RightModule R E))))
    (dgModuleFunctorResolutionReplacementLift_down R (RightModule R E) E (DGFunctor.id
      (RightModule R E)))
end SerrePositivity.InfinityCategories
