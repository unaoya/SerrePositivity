module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseAugmentationPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.DerivedNerveStructure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseDerivedStructure

/-! 共通対象宇宙では、一般宇宙の構造変換は先に構成した全単体族の同じ持ち上げ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

lemma dgGluingUniverseAugmentationPrism_specialization (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) n) (β : (Δ[1] : SSet) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseAugmentationPrism R C D M).app (Opposite.op ⦋n⦌) (ULift.up s, β) =
    ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationNerveHomotopy R C D M).h.app
      (Opposite.op ⦋n⦌) (s, β)) := by
  apply ULift.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)) (stdSimplex.objEquiv β).toOrderHom).toSimplexData =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)) (stdSimplex.objEquiv β).toOrderHom).toSimplexData.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R C))).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R C))
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_id]

lemma dgGluingUniverseDerivedAugmentationHomotopy_specialization (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) n) (β : (Δ[1] : SSet) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedAugmentationHomotopy R C D M).h.app
      (Opposite.op ⦋n⦌) (ULift.up s, β) =
    ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationHomotopy R C D M).h.app
      (Opposite.op ⦋n⦌) (s, β)) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, max (u + 1) v, max (u + 1) v} R C).app
      (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseAugmentationPrism R C D M).app (Opposite.op ⦋n⦌) (ULift.up s, β)) = _
  rw [dgGluingUniverseAugmentationPrism_specialization]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
