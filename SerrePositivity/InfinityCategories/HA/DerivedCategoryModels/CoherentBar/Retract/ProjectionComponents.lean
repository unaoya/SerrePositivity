module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Unconditional
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StableProjectionCompatibility
public import SerrePositivity.DifferentialGraded.Module.Disk
/-!
概要：正規化 bar への実閉射影は、元の次数付き射影と同じ成分を持つ。
方針：MC 射の閉零サイクルを評価し、元の次数付き包含による切断を保つ。
規約：切断には鎖条件を課さない。閉包含は安定自己写像によって別に補正する。
使われ方：修正包含の閉性と射影との分裂式を、同じ全次数 dg 作用のもとで検証する。
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

lemma dgCoherentBarNormalizedModuleProjection_evaluation_f (x : D) (n : ℤ) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC)).f n =
    ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f n := by
  have h := _root_.SerrePositivity.DifferentialGraded.moduleEvaluation_cochain R D x
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC)
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartanMap,
    _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle_cycle] at h
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartanMapElement at h
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomElementMk_π] at h
  have hv := congrArg (fun c => c.v n n (add_zero n)) h
  have ho := moduleEvaluation_cochain R D x (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)
  have hov := congrArg (fun c => c.v n n (add_zero n)) ho
  exact hv.trans hov.symm

abbrev dgCoherentBarNormalizedGradedSection (x : D) (n : ℤ) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).obj
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC))).X n ⟶
    ((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarObject R D F hMC)).X n :=
  ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedInclusion R D F)).f n

lemma dgCoherentBarNormalizedGradedSection_projection (x : D) (n : ℤ) :
    dgCoherentBarNormalizedGradedSection R D F hMC x n ≫
      ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC)).f n = 𝟙 _ := by
  rw [dgCoherentBarNormalizedModuleProjection_evaluation_f]
  change ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedInclusion R D F)).f n ≫ _ = _
  rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedInclusion_projection, CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
  rfl

lemma dgCoherentBarNormalizedGradedSection_naturality
    (x y : D) (q i j : ℤ) (hij : i + q = j)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R (Opposite.op x) (Opposite.op y) q) :
    _root_.SerrePositivity.DifferentialGraded.moduleActionComponent R D
        (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC))
        x y q i j hij f ≫ dgCoherentBarNormalizedGradedSection R D F hMC y j =
      dgCoherentBarNormalizedGradedSection R D F hMC x i ≫
        moduleActionComponent R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarObject R D F hMC) x y q i j hij f := by
  exact moduleMorphism_actionComponent R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedInclusion R D F)
    x y q i j hij f

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
