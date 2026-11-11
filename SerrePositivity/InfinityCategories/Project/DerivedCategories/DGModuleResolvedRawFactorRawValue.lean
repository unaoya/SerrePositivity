module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedRawFactorUnfold
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
lemma dgModuleResolvedInfinity_precompIso_Id_raw_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E))) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) := by
  have hTarget : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R
        (RightModule R E))) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R (RightModule R E) E
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun J => J ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R (RightModule R E) E
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor_up_eq R C E F)).trans (Category.assoc _ _ _))
  have h₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso_Id_unfold_heq R C E F
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso R C (RightModule R E) E F (DGFunctor.id (RightModule
      R E))).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R C (RightModule R E) E F
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) rfl hTarget
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso_Id_heq R C E F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)))
  have h₂ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso R C
    (RightModule R E) E F (DGFunctor.id (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u,
    max (u + 1) v, max (u + 1) v} R C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max
    (u + 1) v} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))))
  have hRawTarget : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
    (RightModule R E))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (RightModule
    R E) E (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R (RightModule R E) E (DGFunctor.id (RightModule R
        E)))) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))) :=
    (congrArg (fun J => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) ≫ J)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity_down_eq R (RightModule R E) E (DGFunctor.id
        (_root_.SerrePositivity.DifferentialGraded.RightModule R E))).symm).trans
      (Category.assoc _ _ _).symm
  have h₃ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso R C (RightModule R E) E F (DGFunctor.id (RightModule
      R E))).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity_down_eq R C E (F.comp (DGFunctor.id (RightModule R
      E)))).symm hRawTarget
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso_Id_down_heq R C E F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
  exact h₀.trans (h₁.trans (h₂.trans h₃))
lemma dgModuleResolvedInfinity_rawFactorIso_raw_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C E F)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso_heq R C E F).trans
    (dgModuleResolvedInfinity_precompIso_Id_raw_heq R C E F)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
