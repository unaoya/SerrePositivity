module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorUnfold
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
lemma dgModuleResolvedInfinity_precompIso_Id_raw_heq :
    HEq (dgModuleResolvedInfinity_precompIso R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E))) ((dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) := by
  have hTarget : (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) ≫
    ((dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) ≫
    (dgModuleOutputResolutionInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))) =
      (dgNerve.map F) ≫ (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R
        (RightModule R E))) ≫ (dgModuleOutputResolutionInfinity R (RightModule R E) E
        (DGFunctor.id (RightModule R E))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun J => J ≫ (dgModuleOutputResolutionInfinity R (RightModule R E) E
        (DGFunctor.id (RightModule R E))))
        (dgModuleResolutionLiftedInputFunctor_up_eq R C E F)).trans (Category.assoc _ _ _))
  have h₀ := dgModuleResolvedInfinity_precompIso_Id_unfold_heq R C E F
  have h₁ := F2.functorIso_postcomp_heq_of_heq
    ((dgModuleOutputResolution_precompIso R C (RightModule R E) E F (DGFunctor.id (RightModule
      R E))).precomp (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
      (dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E))) rfl hTarget
    (dgModuleOutputResolution_unliftedPrecompIso_Id_heq R C E F) (dgNerve.map
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (SemifreeDGModules R E)))
  have h₂ := heq_of_eq (F2.functorIso_precomp_postcomp (dgModuleOutputResolution_precompIso R C
    (RightModule R E) E F (DGFunctor.id (RightModule R E))) (dgNerve.map (dgUniverseLiftUp.{u,
    max (u + 1) v, max (u + 1) v} R C)) (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max
    (u + 1) v} R (SemifreeDGModules R E))))
  have hRawTarget : (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) ≫
    (dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule
    R E) E (DGFunctor.id (RightModule R E)))) =
      ((dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) ≫
        (dgModuleOutputResolutionInfinity R (RightModule R E) E (DGFunctor.id (RightModule R
        E)))) ≫ (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (SemifreeDGModules R E))) :=
    (congrArg (fun J => (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) ≫ J)
      (dgModuleOutputResolutionInfinity_down_eq R (RightModule R E) E (DGFunctor.id
        (RightModule R E))).symm).trans
      (Category.assoc _ _ _).symm
  have h₃ := F2.functorIso_precomp_heq_of_heq (dgModuleOutputResolution_rawFactorPrecompIso R C E F)
    ((dgModuleOutputResolution_precompIso R C (RightModule R E) E F (DGFunctor.id (RightModule
      R E))).postcomp (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
      (SemifreeDGModules R E))))
    (dgModuleOutputResolutionInfinity_down_eq R C E (F.comp (DGFunctor.id (RightModule R
      E)))).symm hRawTarget
    (dgModuleOutputResolution_precompIso_Id_down_heq R C E F) (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
  exact h₀.trans (h₁.trans (h₂.trans h₃))
lemma dgModuleResolvedInfinity_rawFactorIso_raw_heq :
    HEq (dgModuleResolvedInfinity_rawFactorIso R C E F)
      ((dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) :=
  (dgModuleResolvedInfinity_rawFactorIso_heq R C E F).trans
    (dgModuleResolvedInfinity_precompIso_Id_raw_heq R C E F)
end SerrePositivity.InfinityCategories
