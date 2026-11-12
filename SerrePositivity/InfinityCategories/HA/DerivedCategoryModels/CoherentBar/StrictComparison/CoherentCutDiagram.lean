module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutTransition

/-!
概要：実 dg 段階の可算図式と全正規化 bar への余錐。
方針：全 bar への包含の単射性で図式の法則を反映する。
規約：各射は元の θ と可換な実 dg 加群射。
使われ方：全 bar を有限次元段階の余極限として回収する。
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

lemma dgCoherentBarCutModuleInclusion_cancel (n : ℕ) {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    {f g : M ⟶ ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModule R D G n)}
    (h : f ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleInclusion R D G n =
      g ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleInclusion R D G n) : f = g := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext
  intro x
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleInclusion_injective R D G n x q
  have hz := congrArg (fun k : M ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G) =>
      (((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map k).f q) z) h
  simpa only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.comp_apply] using! hz

def dgCoherentBarCutModuleDiagram : ℕ ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D where
  obj n := ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModule R D G n)
  map f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleMap R D G (leOfHom f)
  map_id n := by
    apply dgCoherentBarCutModuleInclusion_cancel R D G n
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleMap_inclusion, Category.id_comp]
  map_comp f g := by
    apply dgCoherentBarCutModuleInclusion_cancel R D G _
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleMap_inclusion, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleMap_inclusion, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleMap_inclusion]

def dgCoherentBarCutModuleCocone : Cocone (dgCoherentBarCutModuleDiagram R D G) where
  pt := ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G)
  ι :=
    { app n := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleInclusion R D G n
      naturality _ _ f := by
        simpa only [dgCoherentBarCutModuleDiagram, Functor.const_obj_obj,
          Functor.const_obj_map, Category.comp_id] using!
          _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleMap_inclusion R D G (leOfHom f) }

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
