module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedChangeRawValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionChangeComparisonHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedRawFactorNaturality
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
def dgModuleOutputResolution_rawFactorPrecompIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id
      (RightModule R E)))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E
      (F.comp (DGFunctor.id (RightModule R E)))))) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R
      (_root_.SerrePositivity.DifferentialGraded.RightModule R E) E (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp
    (DGFunctor.id (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R
    (RightModule R E) E (DGFunctor.id (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C E F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E F (DGFunctor.id (RightModule R
    E)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E (F.comp (DGFunctor.id
    (RightModule R E))))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (RightModule R
    E) E (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_left_source_lift R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_left_output R C E F)
lemma dgModuleOutputResolution_precompIso_Id_down_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso R C (RightModule R E) E F (DGFunctor.id
      (RightModule R E))).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u +
      1) v} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)))) (dgModuleOutputResolution_rawFactorPrecompIso R C E F)
      := by
  have hS := congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor_sourceLift R C (RightModule R E) E F (DGFunctor.id
      (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
  have hR := congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor_replacementLift R C (RightModule R E) E F (DGFunctor.id
      (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at hS hR
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso dgModuleOutputResolution_rawFactorPrecompIso
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso_postcomp_heq_of_outputs
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E (F.comp (DGFunctor.id (RightModule R
      E)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E
      (DGFunctor.id (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionLiftedInputFunctor R C
      E F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R C (RightModule R E) E F
      (DGFunctor.id (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift
      R C E (F.comp (DGFunctor.id (RightModule R E))))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift R (RightModule R E) E (DGFunctor.id
      (RightModule R E)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E (F.comp
      (DGFunctor.id (RightModule R E))))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R
      (_root_.SerrePositivity.DifferentialGraded.RightModule R E) E (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))) hS hR
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentity_left_output R C E F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u,
      max (u + 1) v, max (u + 1) v} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift_down R C E (F.comp (DGFunctor.id (RightModule R E))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift_down R (RightModule R E) E (DGFunctor.id
      (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
