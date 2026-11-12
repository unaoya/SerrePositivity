module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerShortExact
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerCoefficients

/-!
概要：実 coherent bar の零段階を零次元層へ同定する。
方針：零次元支持では層射影と包含が互いに逆であることを示す。
規約：実微分に関する複体同型を作る。
使われ方：最終ホモロジー比較の頂点側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarZeroLayer_recover (x : D) (q : ℤ)
    (z : (moduleDegreeEvaluation R D x q).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q 0) :
    (moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G 0)
      ((moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G 0) z) = z := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G 0 ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G 0 -
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G
  have hf : ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I, s.1 ≤ 0 →
      Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s ≫ f = 0 := by
    intro s hs
    dsimp only [f]
    rw [Preadditive.comp_sub,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection_raw_ι_of_eq R D G 0 s (by omega), sub_self]
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarDegreeFiltration_annihilate R D G f x q 0 hf a ha
  change (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).map f a = 0 at h
  change ((_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).map f).hom a = 0 at h
  simpa only [f, CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_comp,
    ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.comp_apply, sub_eq_zero] using! h

lemma dgCoherentBarZeroStageToLayer_injective (x : D) (q : ℤ) :
    Function.Injective ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x 0).f q) := by
  intro a b h
  apply Subtype.ext
  have hh := congrArg ((_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).map
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G 0)) h
  change (moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G 0)
      ((moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G 0) a.val) =
    (moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G 0)
      ((moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G 0) b.val) at hh
  rwa [dgCoherentBarZeroLayer_recover R D G x q a.val a.property,
    dgCoherentBarZeroLayer_recover R D G x q b.val b.property] at hh

def dgCoherentBarZeroStageIso (x : D) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x 0 ≅
      (moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G 0) := by
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x 0
  letI : Mono f := HomologicalComplex.mono_of_mono_f f (fun q =>
    (ModuleCat.mono_iff_injective _).mpr (dgCoherentBarZeroStageToLayer_injective R D G x q))
  letI : Epi f := HomologicalComplex.epi_of_epi_f f (fun q =>
    (ModuleCat.epi_iff_surjective _).mpr (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer_surjective R D G x q 0))
  letI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
