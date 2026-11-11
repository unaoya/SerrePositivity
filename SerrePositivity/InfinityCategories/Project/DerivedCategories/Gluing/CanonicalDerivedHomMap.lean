module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModuleResolutionSection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ResolutionProjectiveSourceHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorQuasiIsoFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan

/-! 元の導来比較そのものは、射影的始域からの全写像空間を保存する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]

lemma dgGluingModuleDerivedHomMap_equivalence (N P : _root_.SerrePositivity.DifferentialGraded.RightModule R C)
    (hN : _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R C (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C
        (DGFunctor.id (RightModule R C))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)) := by
  let F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R C) (_root_.SerrePositivity.DifferentialGraded.RightModule R C) := _root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R C)
  let S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleResolutionSection R (RightModule R C) C F
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleResolutionSection_isQCatEquivalence R (RightModule R C) C F
  have hs := he.isFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (RightModule R C) C F))
        (S.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)) (S.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P))) := by
    dsimp only [S]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleResolutionSection_vertex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleResolutionSection_vertex]
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_pinchedHomMap_quasiIso_equivalence
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolutionProjectiveSource_replacement_quasiIso
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionObject_source] using hN
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleResolutionSection_replacement, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp]
  exact hs.comp hr

lemma dgGluingModuleDerivedRepresentableHomMap_equivalence (c : C) (N : _root_.SerrePositivity.DifferentialGraded.RightModule R C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R C)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (representable R c)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)) :=
  dgGluingModuleDerivedHomMap_equivalence R C _ _ (_root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective R C c)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
