module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ProjectionComponents
/-!
概要：安定した実 bar 自己写像の成分と、正規化射影との整合式を公開する。
方針：既存の安定作用素のサイクルと射影像の等式を、評価成分へ移す。
規約：恒等への鎖ホモトピーと退化因子の消去を区別する。
使われ方：修正包含の分裂式と、変形 retract の同じ射影の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarNormalizationEndomorphism_evaluation_f (x : D) (n : ℤ) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphism R D F hMC)).f n =
      ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) x).f 0
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationProjectorGraded R D F)).v n n (add_zero n) := by
  have h := _root_.SerrePositivity.DifferentialGraded.moduleEvaluation_cochain R D x
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphism R D F hMC)
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphism_cycle] at h
  have hv := congrArg (fun c => c.v n n (add_zero n)) h
  exact hv.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarEndRebase_π R D F hMC 0
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationProjectorGraded R D F) x n n (add_zero n))

lemma dgCoherentBarNormalizationEndomorphism_projection :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphism R D F hMC ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext
  intro x
  apply HomologicalComplex.Hom.ext
  funext n
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    dgCoherentBarNormalizationEndomorphism_evaluation_f,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleProjection_evaluation_f]
  have h := congrArg (fun z => ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D F)) x).f 0 z).v
      n n (add_zero n))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationProjectorGraded_normalizedProjection R D F hMC)
  simp only [_root_.SerrePositivity.DifferentialGraded.moduleHomWhiskerLeft_apply_π, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, _root_.SerrePositivity.DifferentialGraded.yoneda_moduleUnit_π] at h
  simpa only [Cochain.ofHom_v, HomologicalComplex.id_f, Category.id_comp] using h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
