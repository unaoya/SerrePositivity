module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitCapPastingTriangles
/-!
概要：元終域の六貼り合わせ片を、二単体全域で同じ二端点に固定する。
方針：元の四入力道の実対角へ端点退化を戻す。
規約：六片と全入力を変更しない。使われ方：同じ写像空間への六二単体の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetFirstUnitPastingInputPath (i : Fin 6) :=
  if i = 0 ∨ i = 1 ∨ i = 4 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath R C D E p q X Y
    else _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y

lemma dgGluingHomTargetUnitCapPastingSourceSide_evaluation (i : Fin 6) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingSourceSide i) P ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomTargetFirstUnitPastingInputPath R C D E p q X Y i ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingSourceSide_reindex]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron_three R C D E p q X Y]
  by_cases hi : i = 0 ∨ i = 1 ∨ i = 4
  · simp only [dgGluingHomTargetFirstUnitPastingInputPath, hi, ite_true]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreUnitCapTriangleFamily_reindex R C D E p q X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreUnitCapTriangleFamily_diagonal R C D E p q X Y]
  · simp only [dgGluingHomTargetFirstUnitPastingInputPath, hi, ite_false]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily_reindex R C D E p q X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily_diagonal R C D E p q X Y]

def dgGluingHomTargetLastUnitPastingInputPath (i : Fin 6) :=
  if i = 2 ∨ i = 3 ∨ i = 4 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath R C D E p q X Y
    else _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath R C D E p q X Y

lemma dgGluingHomTargetUnitCapPastingTargetSide_evaluation (i : Fin 6) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismParameterReindex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTargetSide i) P ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomTargetLastUnitPastingInputPath R C D E p q X Y i ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingTargetSide_reindex]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron_zero R C D E p q X Y]
  by_cases hi : i = 2 ∨ i = 3 ∨ i = 4
  · simp only [dgGluingHomTargetLastUnitPastingInputPath, hi, ite_true]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitUnitCapTriangleFamily_reindex R C D E p q X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitUnitCapTriangleFamily_diagonal R C D E p q X Y]
  · simp only [dgGluingHomTargetLastUnitPastingInputPath, hi, ite_false]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitUnitCollarTriangleFamily_reindex R C D E p q X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitUnitCollarTriangleFamily_diagonal R C D E p q X Y]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_source (i : Fin 6) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] ⊗ P) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y i =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_source_retract]
  simp only [Category.assoc]
  rw [dgGluingHomTargetUnitCapPastingSourceSide_evaluation R C D E p q X Y i]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 0
    (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero, SSet.comp_const, SSet.comp_const]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_target (i : Fin 6) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ P) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y i =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_target_retract]
  simp only [Category.assoc]
  rw [dgGluingHomTargetUnitCapPastingTargetSide_evaluation R C D E p q X Y i]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 1
    (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one, SSet.comp_const, SSet.comp_const]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
