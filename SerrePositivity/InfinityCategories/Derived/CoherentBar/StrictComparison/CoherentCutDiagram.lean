module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutTransition

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarCutModuleInclusion_cancel (n : ℕ) {M : ModuleCategory R D}
    {f g : M ⟶ ForgetEnrichment.of (Complex R) (dgCoherentBarCutModule R D G n)}
    (h : f ≫ dgCoherentBarCutModuleInclusion R D G n =
      g ≫ dgCoherentBarCutModuleInclusion R D G n) : f = g := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply dgCoherentBarCutModuleInclusion_injective R D G n x q
  have hz := congrArg (fun k : M ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G) =>
      (((moduleEvaluation R D x).map k).f q) z) h
  simpa only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.comp_apply] using! hz

def dgCoherentBarCutModuleDiagram : ℕ ⥤ ModuleCategory R D where
  obj n := ForgetEnrichment.of (Complex R) (dgCoherentBarCutModule R D G n)
  map f := dgCoherentBarCutModuleMap R D G (leOfHom f)
  map_id n := by
    apply dgCoherentBarCutModuleInclusion_cancel R D G n
    rw [dgCoherentBarCutModuleMap_inclusion, Category.id_comp]
  map_comp f g := by
    apply dgCoherentBarCutModuleInclusion_cancel R D G _
    rw [dgCoherentBarCutModuleMap_inclusion, Category.assoc,
      dgCoherentBarCutModuleMap_inclusion, dgCoherentBarCutModuleMap_inclusion]

def dgCoherentBarCutModuleCocone : Cocone (dgCoherentBarCutModuleDiagram R D G) where
  pt := ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G)
  ι :=
    { app n := dgCoherentBarCutModuleInclusion R D G n
      naturality _ _ f := by
        simpa only [dgCoherentBarCutModuleDiagram, Functor.const_obj_obj,
          Functor.const_obj_map, Category.comp_id] using!
          dgCoherentBarCutModuleMap_inclusion R D G (leOfHom f) }

end SerrePositivity.InfinityCategories
