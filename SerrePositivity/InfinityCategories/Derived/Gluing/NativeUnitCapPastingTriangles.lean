module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCapDiagonalPastingFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitCapDiagonalEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitCollarDiagonalEvaluation
/-! # 同じ導来四面体上の係数側六三角形

概要：六つの貼り合わせ片を元 Hom 全体の native augmentation 四面体へ適用する。
方針：共有辺と二つの実単位補正対角を厳密に回収する。
規約：六片は同じ四面体を使い、元入力や実補正道を変更しない。
使われ方：係数側の高次合成等式を、左右実補正対角の合成へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativeUnitCapPastingTriangleFamily (i : Fin 6) :=
  dgGluingUnitCapPastingDomain i P ≫
    dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y

lemma dgGluingNativeUnitCapPastingTriangleFamily_first_diagonal :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 0 =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 1 := by
  simp only [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_first_diagonal]

lemma dgGluingNativeUnitCapPastingTriangleFamily_last_diagonal :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 2 =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 3 := by
  simp only [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_last_diagonal]

lemma dgGluingNativeUnitCapPastingTriangleFamily_first_bridge :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 1 =
      (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 5 := by
  simp only [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_first_bridge]

lemma dgGluingNativeUnitCapPastingTriangleFamily_last_bridge :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 3 =
      (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 5 := by
  simp only [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_last_bridge]

lemma dgGluingNativeUnitCapPastingTriangleFamily_coefficient_first :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 1 =
      (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 4 := by
  simp only [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_coefficient_first]

lemma dgGluingNativeUnitCapPastingTriangleFamily_coefficient_last :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 3 =
      (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 4 := by
  simp only [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_coefficient_last]

lemma dgGluingNativeUnitCapPastingTriangleFamily_collar_bridge :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 5 =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCollarDiagonalTriangleFamily R C D M X Y := by
  simp only [dgGluingNativeUnitCapPastingTriangleFamily,
    dgGluingNativeUnitCollarDiagonalTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_collar_bridge]

lemma dgGluingNativeUnitCapPastingTriangleFamily_first_cap :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 0 =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom) ≫
        intervalMappingUncurry (dgGluingNativePreCapInputPath R C D M X Y ≫
          dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_first_cap]
  simp only [Category.assoc]
  rw [dgGluingNativeNormalizationAugmentationTetrahedron_three R C D M X Y]
  rw [← dgGluingNativePreUnitCapTriangleFamily_reindex R C D M X Y,
    dgGluingNativePreCapInputPath_diagonal_evaluation R C D M X Y]

lemma dgGluingNativeUnitCapPastingTriangleFamily_last_cap :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 2 =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom) ≫
        intervalMappingUncurry (dgGluingNativeExitCapInputPath R C D M X Y ≫
          dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_last_cap]
  simp only [Category.assoc]
  rw [dgGluingNativeNormalizationAugmentationTetrahedron_zero R C D M X Y]
  rw [dgGluingNativeNormalizationExitAugmentationTriangle_eq R C D M X Y]
  rw [← dgGluingNativeExitUnitCapTriangleFamily_reindex R C D M X Y,
    dgGluingNativeExitCapInputPath_diagonal_evaluation R C D M X Y]
end SerrePositivity.InfinityCategories
