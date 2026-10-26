module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapPastingTriangles
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetFirstUnitPastingInputPath (i : Fin 6) :=
  if i = 0 ∨ i = 1 ∨ i = 4 then dgGluingHomTargetPreCapInputPath R C D E p q X Y
    else dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y

lemma dgGluingHomTargetUnitCapPastingSourceSide_evaluation (i : Fin 6) :
    dgGluingPrismParameterReindex (dgGluingUnitCapPastingSourceSide i) P ≫
        dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom) ≫
        intervalMappingUncurry (dgGluingHomTargetFirstUnitPastingInputPath R C D E p q X Y i ≫
          dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  rw [dgGluingUnitCapPastingSourceSide_reindex]
  simp only [Category.assoc]
  rw [dgGluingHomTargetAugmentationTetrahedron_three R C D E p q X Y]
  by_cases hi : i = 0 ∨ i = 1 ∨ i = 4
  · simp only [dgGluingHomTargetFirstUnitPastingInputPath, hi, ite_true]
    rw [← dgGluingHomTargetPreUnitCapTriangleFamily_reindex R C D E p q X Y,
      dgGluingHomTargetPreUnitCapTriangleFamily_diagonal R C D E p q X Y]
  · simp only [dgGluingHomTargetFirstUnitPastingInputPath, hi, ite_false]
    rw [← dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily_reindex R C D E p q X Y,
      dgGluingHomTargetPreNormalizeUnitCollarTriangleFamily_diagonal R C D E p q X Y]

def dgGluingHomTargetLastUnitPastingInputPath (i : Fin 6) :=
  if i = 2 ∨ i = 3 ∨ i = 4 then dgGluingHomTargetExitCapInputPath R C D E p q X Y
    else dgGluingHomTargetExitCollarInputPath R C D E p q X Y

lemma dgGluingHomTargetUnitCapPastingTargetSide_evaluation (i : Fin 6) :
    dgGluingPrismParameterReindex (dgGluingUnitCapPastingTargetSide i) P ≫
        dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom) ≫
        intervalMappingUncurry (dgGluingHomTargetLastUnitPastingInputPath R C D E p q X Y i ≫
          dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  rw [dgGluingUnitCapPastingTargetSide_reindex]
  simp only [Category.assoc]
  rw [dgGluingHomTargetAugmentationTetrahedron_zero R C D E p q X Y]
  by_cases hi : i = 2 ∨ i = 3 ∨ i = 4
  · simp only [dgGluingHomTargetLastUnitPastingInputPath, hi, ite_true]
    rw [← dgGluingHomTargetExitUnitCapTriangleFamily_reindex R C D E p q X Y,
      dgGluingHomTargetExitUnitCapTriangleFamily_diagonal R C D E p q X Y]
  · simp only [dgGluingHomTargetLastUnitPastingInputPath, hi, ite_false]
    rw [← dgGluingHomTargetExitUnitCollarTriangleFamily_reindex R C D E p q X Y,
      dgGluingHomTargetExitUnitCollarTriangleFamily_diagonal R C D E p q X Y]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_source (i : Fin 6) :
    prismEndpoint 0 (Δ[2] ⊗ P) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y i =
      SSet.const (Simplex.vertex (p.obj X.left)) := by
  rw [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_source_retract]
  simp only [Category.assoc]
  rw [dgGluingHomTargetUnitCapPastingSourceSide_evaluation R C D E p q X Y i]
  rw [reassoc_of% (prismEndpoint_naturality 0
    (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom)]
  rw [intervalMappingUncurry_zero, SSet.comp_const, SSet.comp_const]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_target (i : Fin 6) :
    prismEndpoint 1 (Δ[2] ⊗ P) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y i =
      SSet.const (Simplex.vertex (q.obj Y.right)) := by
  rw [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_target_retract]
  simp only [Category.assoc]
  rw [dgGluingHomTargetUnitCapPastingTargetSide_evaluation R C D E p q X Y i]
  rw [reassoc_of% (prismEndpoint_naturality 1
    (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom)]
  rw [intervalMappingUncurry_one, SSet.comp_const, SSet.comp_const]
end SerrePositivity.InfinityCategories
