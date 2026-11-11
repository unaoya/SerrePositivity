module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionChangeActionUnlift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomConjugationPrecomp
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyInputExchange
/-!
概要：指定済みの実出力分解の比較の射を、同じ元の nerve 作用へ照合する。
方針：全関手射の上げ下げと指定逆を保つ共役式を使う。
規約：比較の値を再選択しない。使われ方：導来 kernel の準同型比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
lemma dgModuleResolvedInfinity_rawFactor_target_eq
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule
      R E))) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R
      (_root_.SerrePositivity.DifferentialGraded.RightModule R E) E (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))) := by
  have hL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement R (RightModule R E) E (DGFunctor.id
    (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  have hF := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor_up_eq R C E F
  exact (congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫ t) hL).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule
        R E) E (DGFunctor.id (RightModule R E))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (RightModule R E) E (DGFunctor.id (RightModule R
        E)))))) hF.symm).trans (Category.assoc _ _ _)))
lemma dgModuleResolvedInfinity_rawFactor_hom_raw_heq (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C E F).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq_of_endpoint_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C E F)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement R C E F)
    (dgModuleResolvedInfinity_rawFactor_target_eq R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso_raw_heq R C E F)
lemma dgModuleResolvedInfinity_rawFactor_inv_raw_heq (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C E F).inv
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).inv :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_inv_heq_of_endpoint_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C E F)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement R C E F)
    (dgModuleResolvedInfinity_rawFactor_target_eq R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso_raw_heq R C E F)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
