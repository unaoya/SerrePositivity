module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModuleResolutionSection
public import SerrePositivity.InfinityCategories.Derived.Gluing.ResolutionProjectiveSourceHom
public import SerrePositivity.InfinityCategories.Derived.DGFunctorQuasiIsoFullyFaithful
public import SerrePositivity.InfinityCategories.Core.MappingSpaceRightKan

/-! 元の導来比較そのものは、射影的始域からの全写像空間を保存する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingModuleDerivedHomMap_equivalence (N P : RightModule R C)
    (hN : moduleHomotopicallyProjective R C (ForgetEnrichment.of (Complex R) N)) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap (dgModuleResolvedInfinity R (RightModule R C) C
        (DGFunctor.id (RightModule R C))) (Simplex.vertex N) (Simplex.vertex P)) := by
  let F : DGFunctor R (RightModule R C) (RightModule R C) := DGFunctor.id (RightModule R C)
  let S := dgGluingModuleResolutionSection R (RightModule R C) C F
  have he := dgGluingModuleResolutionSection_isQCatEquivalence R (RightModule R C) C F
  have hs := he.isFullyFaithful (Simplex.vertex N) (Simplex.vertex P)
  have hr : IsSimplicialHomotopyEquivalence
      (pinchedHomMap (dgNerve.map (dgModuleFunctorResolutionReplacement R (RightModule R C) C F))
        (S.app _ (Simplex.vertex N)) (S.app _ (Simplex.vertex P))) := by
    dsimp only [S]
    rw [dgGluingModuleResolutionSection_vertex, dgGluingModuleResolutionSection_vertex]
    apply dgFunctor_pinchedHomMap_quasiIso_equivalence
    apply dgGluingResolutionProjectiveSource_replacement_quasiIso
    simpa only [dgModuleOutputResolutionObject_source] using hN
  rw [← dgGluingModuleResolutionSection_replacement, pinchedHomMap_comp]
  exact hs.comp hr

lemma dgGluingModuleDerivedRepresentableHomMap_equivalence (c : C) (N : RightModule R C) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap (dgModuleResolvedInfinity R (RightModule R C) C
        (DGFunctor.id (RightModule R C)))
        (Simplex.vertex (representable R c)) (Simplex.vertex N)) :=
  dgGluingModuleDerivedHomMap_equivalence R C _ _ (representable_homotopicallyProjective R C c)

end SerrePositivity.InfinityCategories
