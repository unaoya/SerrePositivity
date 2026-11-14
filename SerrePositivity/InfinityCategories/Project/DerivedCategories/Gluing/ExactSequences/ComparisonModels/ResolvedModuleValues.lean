module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleOutputResolutionAugmentation

/-! gluing が使う同じ全加群の導来比較の頂点と、その元の augmentation。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]

def dgGluingResolvedModule (N : RightModule R C) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R C :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionValue R (RightModule R C) C (DGFunctor.id (RightModule R C)) N

def dgGluingResolvedModuleAugmentation (N : _root_.SerrePositivity.DifferentialGraded.RightModule R C) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgGluingResolvedModule R C N).val ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation R (RightModule R C) C
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R C)) N

lemma dgGluingResolvedModuleAugmentation_quasiIso (N : _root_.SerrePositivity.DifferentialGraded.RightModule R C) :
    _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R C (dgGluingResolvedModuleAugmentation R C N) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation_quasiIso R (RightModule R C) C
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R C)) N

lemma dgGluingResolvedModule_projective (N : _root_.SerrePositivity.DifferentialGraded.RightModule R C) :
    _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R C
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgGluingResolvedModule R C N).val) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R C _

lemma dgGluingModuleDerivedComparison_vertex (N : _root_.SerrePositivity.DifferentialGraded.RightModule R C) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C
      (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (dgGluingResolvedModule R C N) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R C))).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R (RightModule R C) C
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R C))).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R C)).obj N))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity_vertex]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
