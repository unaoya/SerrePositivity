module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInfinity
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionAugmentation

/-! gluing が使う同じ全加群の導来比較の頂点と、その元の augmentation。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

def dgGluingResolvedModule (N : RightModule R C) : SemifreeDGModules R C :=
  dgModuleOutputResolutionValue R (RightModule R C) C (DGFunctor.id (RightModule R C)) N

def dgGluingResolvedModuleAugmentation (N : RightModule R C) :
    ForgetEnrichment.of (Complex R) (dgGluingResolvedModule R C N).val ⟶
      ForgetEnrichment.of (Complex R) N :=
  dgModuleOutputResolutionAugmentation R (RightModule R C) C
    (DGFunctor.id (RightModule R C)) N

lemma dgGluingResolvedModuleAugmentation_quasiIso (N : RightModule R C) :
    moduleQuasiIso R C (dgGluingResolvedModuleAugmentation R C N) :=
  dgModuleOutputResolutionAugmentation_quasiIso R (RightModule R C) C
    (DGFunctor.id (RightModule R C)) N

lemma dgGluingResolvedModule_projective (N : RightModule R C) :
    moduleHomotopicallyProjective R C
      (ForgetEnrichment.of (Complex R) (dgGluingResolvedModule R C N).val) :=
  dgSemifreeModule_isProjective R C _

lemma dgGluingModuleDerivedComparison_vertex (N : RightModule R C) :
    (dgModuleResolvedInfinity R (RightModule R C) C
      (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌) (Simplex.vertex N) =
      Simplex.vertex (dgGluingResolvedModule R C N) := by
  change (dgNerve.map (dgUniverseLiftDown R (SemifreeDGModules R C))).app (Opposite.op ⦋0⦌)
    ((dgModuleOutputResolutionInfinity R (RightModule R C) C
      (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌)
      (Simplex.vertex ((dgUniverseLiftUp R (RightModule R C)).obj N))) = _
  rw [dgModuleOutputResolutionInfinity_vertex]
  rfl

end SerrePositivity.InfinityCategories
