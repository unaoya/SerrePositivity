module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutGradedSplitting
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutZero
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentZeroStageIso

/-!
概要：零次元層の内部 dg 加群から実正規化 bar への閉じた包含。
方針：零段階への回収と θ の零段階での消滅を用いる。
規約：内部次数層の包含を実 dg 射として構成する。
使われ方：指定 native 増大の C1 ホモロジー増大との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgBarZeroLayerInclusion_mem (x : D) (q : ℤ)
    (z : ((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G 0)).X q) :
    ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G 0)).f q z ∈
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q 0 := by
  have he := congrArg (fun f : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G 0 ⟶
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G => ((moduleEvaluation R D x).map f).f q z)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion_cut_recover R D G 0)
  simp only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.comp_apply] at he
  rw [← he]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_mem R D G x q 0 _

lemma dgBarZeroLayerInclusion_theta :
    (eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G 0)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G)).f 1 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D G) = 0 := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
  intro x
  apply Cochain.ext
  intro q r hqr
  subst r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  erw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomogeneous_pre_apply R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G 0)
    1 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D G) x q z]
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration_zero_theta R D G x q _
    (dgBarZeroLayerInclusion_mem R D G x q z)
  simpa only [map_zero, Cochain.zero_v, ModuleCat.hom_zero, LinearMap.zero_apply] using! h

def dgBarZeroLayerInclusion : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G 0 ⟶
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarMaurerCartanZeroIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G 0)).inv ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarMaurerCartanModuleMap R D 0 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D G)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarModuleZero_maurerCartan R D _) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta_maurerCartan R D G
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D G))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G 0)
      (by simpa only [map_zero] using! dgBarZeroLayerInclusion_theta R D G)

@[simp]
lemma dgBarZeroLayerInclusion_eval_f (x : D) (q : ℤ) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (dgBarZeroLayerInclusion R D G)).f q =
      ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G 0)).f q := by
  simp only [dgBarZeroLayerInclusion, Functor.map_comp, HomologicalComplex.comp_f,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarMaurerCartanModuleMap_eval_f]
  have hi : ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarMaurerCartanZeroIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G 0)).inv).f q =
      𝟙 (((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G 0)).X q) := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarMaurerCartanZeroIso, moduleIsoMk_inv_eval]
    rfl
  rw [hi, Category.id_comp]

lemma dgBarZeroStage_inclusion (x : D) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageIso R D G x).hom ≫
      (_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (dgBarZeroLayerInclusion R D G) =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, dgBarZeroLayerInclusion_eval_f]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroLayer_recover R D G x q z.val z.property

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
