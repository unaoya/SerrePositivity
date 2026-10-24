module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitCapPastingTriangles
/-! # 導来四面体の六貼り合わせ片の全域端点固定

概要：六片すべての区間両端を、二単体パラメーター全体で固定する。
方針：端点退化を四つの既知の実入力対角道へ戻し、区間評価の端点固定を使う。
規約：頂点だけでなく二単体全体の両端を固定し、単位則を追加しない。
使われ方：係数側の六片を同じ導来写像空間の二単体へ curry する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativeFirstUnitPastingInputPath (i : Fin 6) :=
  if i = 0 ∨ i = 1 ∨ i = 4 then dgGluingNativePreCapInputPath R C D M X Y
    else dgGluingNativePreCollarInputPath R C D M X Y

lemma dgGluingNativeUnitCapPastingSourceSide_evaluation (i : Fin 6) :
    dgGluingPrismParameterReindex (dgGluingUnitCapPastingSourceSide i) P ≫
        dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom) ≫
        intervalMappingUncurry (dgGluingNativeFirstUnitPastingInputPath R C D M X Y i ≫
          dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingUnitCapPastingSourceSide_reindex]
  simp only [Category.assoc]
  rw [dgGluingNativeNormalizationAugmentationTetrahedron_three R C D M X Y]
  by_cases hi : i = 0 ∨ i = 1 ∨ i = 4
  · simp only [dgGluingNativeFirstUnitPastingInputPath, hi, ite_true]
    rw [← dgGluingNativePreUnitCapTriangleFamily_reindex R C D M X Y,
      dgGluingNativePreCapInputPath_diagonal_evaluation R C D M X Y]
  · simp only [dgGluingNativeFirstUnitPastingInputPath, hi, ite_false]
    rw [← dgGluingNativePreNormalizeUnitCollarTriangleFamily_reindex R C D M X Y,
      dgGluingNativePreCollarInputPath_diagonal_evaluation R C D M X Y]

def dgGluingNativeLastUnitPastingInputPath (i : Fin 6) :=
  if i = 2 ∨ i = 3 ∨ i = 4 then dgGluingNativeExitCapInputPath R C D M X Y
    else dgGluingNativeExitCollarInputPath R C D M X Y

lemma dgGluingNativeUnitCapPastingTargetSide_evaluation (i : Fin 6) :
    dgGluingPrismParameterReindex (dgGluingUnitCapPastingTargetSide i) P ≫
        dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom) ≫
        intervalMappingUncurry (dgGluingNativeLastUnitPastingInputPath R C D M X Y i ≫
          dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingUnitCapPastingTargetSide_reindex]
  simp only [Category.assoc]
  rw [dgGluingNativeNormalizationAugmentationTetrahedron_zero R C D M X Y,
    dgGluingNativeNormalizationExitAugmentationTriangle_eq R C D M X Y]
  by_cases hi : i = 2 ∨ i = 3 ∨ i = 4
  · simp only [dgGluingNativeLastUnitPastingInputPath, hi, ite_true]
    rw [← dgGluingNativeExitUnitCapTriangleFamily_reindex R C D M X Y,
      dgGluingNativeExitCapInputPath_diagonal_evaluation R C D M X Y]
  · simp only [dgGluingNativeLastUnitPastingInputPath, hi, ite_false]
    rw [← dgGluingNativeExitUnitCollarTriangleFamily_reindex R C D M X Y,
      dgGluingNativeExitCollarInputPath_diagonal_evaluation R C D M X Y]

lemma dgGluingNativeUnitCapPastingTriangleFamily_source (i : Fin 6) :
    prismEndpoint 0 (Δ[2] ⊗ P) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y i =
      SSet.const ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X.left))) := by
  rw [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_source_retract]
  simp only [Category.assoc]
  rw [dgGluingNativeUnitCapPastingSourceSide_evaluation R C D M X Y i]
  rw [reassoc_of% (prismEndpoint_naturality 0
    (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom)]
  rw [intervalMappingUncurry_zero, SSet.comp_const, SSet.comp_const]

lemma dgGluingNativeUnitCapPastingTriangleFamily_target (i : Fin 6) :
    prismEndpoint 1 (Δ[2] ⊗ P) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y i =
      SSet.const ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex Y.right))) := by
  rw [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_target_retract]
  simp only [Category.assoc]
  rw [dgGluingNativeUnitCapPastingTargetSide_evaluation R C D M X Y i]
  rw [reassoc_of% (prismEndpoint_naturality 1
    (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom)]
  rw [intervalMappingUncurry_one, SSet.comp_const, SSet.comp_const]
end SerrePositivity.InfinityCategories
