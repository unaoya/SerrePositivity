module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Augmentations.NormalizationAugmentationStaircase
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeNormalizationAugmentationTetrahedron
/-! # 正本導来 augmentation 四面体の四つの貼り合わせ片

概要：native 四面体全体の augmentation を実四単体族へ分け、隣接共有面と両端を保持する。
方針：同じ導来四面体に標準階段単体を前合成する。
規約：充填を選び直さず、元 Hom 入力と全 augmentation を保つ。
使われ方：実単位補正三角形と係数面を結ぶ高次貼り合わせを供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y
def dgGluingNativeNormalizationAugmentationStaircase (i : Fin 4) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationStaircaseSimplex i ▷ P) ≫
    ((β_ (Δ[3] : SSet.{max (u + 1) v w}) Δ[1]).hom ▷ P) ≫
      (α_ (Δ[1] : SSet.{max (u + 1) v w}) Δ[3] P).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y

lemma dgGluingNativeNormalizationAugmentationStaircase_shared (i : Fin 3) :
    (stdSimplex.δ i.castSucc.succ ▷ P) ≫
        dgGluingNativeNormalizationAugmentationStaircase R C D M X Y i.castSucc =
      (stdSimplex.δ i.succ.castSucc ▷ P) ≫
        dgGluingNativeNormalizationAugmentationStaircase R C D M X Y i.succ := by
  simp only [dgGluingNativeNormalizationAugmentationStaircase, ← Category.assoc,
    ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationStaircaseSimplex_shared]

lemma dgGluingNativeNormalizationAugmentationStaircase_target :
    (stdSimplex.δ (0 : Fin 5) ▷ P) ≫
        dgGluingNativeNormalizationAugmentationStaircase R C D M X Y 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[3] ⊗ P) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
  calc
    _ = (ι₁ ▷ P) ≫
        ((β_ (Δ[3] : SSet.{max (u + 1) v w}) Δ[1]).hom ▷ P) ≫
        (α_ (Δ[1] : SSet.{max (u + 1) v w}) Δ[3] P).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
      simp only [dgGluingNativeNormalizationAugmentationStaircase, ← Category.assoc,
        ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationStaircaseSimplex_target]
    _ = _ := rfl

lemma dgGluingNativeNormalizationAugmentationStaircase_source :
    (stdSimplex.δ (4 : Fin 5) ▷ P) ≫
        dgGluingNativeNormalizationAugmentationStaircase R C D M X Y 3 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ P) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
  calc
    _ = (ι₀ ▷ P) ≫
        ((β_ (Δ[3] : SSet.{max (u + 1) v w}) Δ[1]).hom ▷ P) ≫
        (α_ (Δ[1] : SSet.{max (u + 1) v w}) Δ[3] P).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
      simp only [dgGluingNativeNormalizationAugmentationStaircase, ← Category.assoc,
        ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationStaircaseSimplex_source]
    _ = _ := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
