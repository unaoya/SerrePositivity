module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCollarDiagonalTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeNormalizationAugmentationTetrahedron
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeExitUnitCollarTriangles
/-! # 同じ導来四面体上の左右実補正対角の三角形

概要：左右補正族の実対角を、元 Hom 全体で同じ導来 augmentation 三角形の二面へ接続する。
方針：有限再添字を native 四面体へ前合成し、その指定第三面・第零面を回収する。
規約：二つの補正道や三角形の代表を変更しない。
使われ方：選択済み二変形への相対比較と、係数面との高次貼り合わせを接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativeUnitCollarDiagonalTriangleFamily :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangleDomain P ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y

lemma dgGluingNativeNormalizationExitAugmentationTriangle_eq :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationExitAugmentationTriangle R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitAugmentationTriangle R C D M X Y := rfl

lemma dgGluingNativeUnitCollarDiagonalTriangleFamily_two :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCollarDiagonalTriangleFamily R C D M X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y := by
  rw [dgGluingNativeUnitCollarDiagonalTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangleDomain_two]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron_three R C D M X Y]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeUnitCollarTriangleFamily_reindex R C D M X Y]

lemma dgGluingNativeUnitCollarDiagonalTriangleFamily_zero :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCollarDiagonalTriangleFamily R C D M X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y := by
  rw [dgGluingNativeUnitCollarDiagonalTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangleDomain_zero]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron_zero R C D M X Y]
  rw [dgGluingNativeNormalizationExitAugmentationTriangle_eq R C D M X Y]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCollarTriangleFamily_reindex R C D M X Y]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
