module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.NativeExitUnitCollarTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.NormalizationUnitCaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseUnitCapFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.TriangleTimeTransport
/-! # native 標準合成面までの元固定辺付き補正

概要：両側の単位補正を元 Hom 入力とともに正本導来関手へ移し、共有補正端を保つ。
方針：共通の時間輸送を使い、両固定辺と元補正族の端を厳密に同定する。
規約：前側の終端と終側の始端は同じ標準射影面であり、三角形を選び直さない。
使われ方：選択済み二変形へ移すための native 入力固定補正族を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory CartesianMonoidalCategory SSet

open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "RM" => _root_.SerrePositivity.DifferentialGraded.RightModule R C
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M Y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativePreUnitCapTriangleFamily :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeTransport.{max (u + 1) v, max (u + 1) v w} 2
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
def dgGluingNativeExitUnitCapTriangleFamily :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeTransport.{max (u + 1) v, max (u + 1) v w} 2
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
lemma dgGluingNativePreUnitCapTriangleFamily_reindex :
    dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativePreUnitCapTriangleFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeTransport]
  have hraw : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCap ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawTriangle R C D M X Y := rfl
  rw [hraw, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_first_cap_reindex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingNativeExitUnitCapTriangleFamily_reindex :
    dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeExitUnitCapTriangleFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeTransport]
  have hraw : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCap ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitAugmentationRawTriangle R C D M X Y := rfl
  rw [hraw, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_last_cap_reindex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingNativePreUnitCapTriangleFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (P ⊗ Δ[1])) ≫ dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      fst (Δ[1] : SSet.{max (u + 1) v w}) (P ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X).edge := by
  have h :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeTransport_fixed_edge.{max (u + 1) v, max (u + 1) v w} 2
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R RM)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R RM (IX).augmentation).edge)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreUnitCapTriangleFamily_first.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  exact h.trans (congrArg (fun g => fst (Δ[1] : SSet.{max (u + 1) v w}) (P ⊗ Δ[1]) ≫ g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarAugmentationEdge R C D M X))
lemma dgGluingNativeExitUnitCapTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (P ⊗ Δ[1])) ≫ dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      fst (Δ[1] : SSet.{max (u + 1) v w}) (P ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y).edge := by
  have h :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeTransport_fixed_edge.{max (u + 1) v, max (u + 1) v w} 0
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R RM)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R RM (IY).augmentation).edge)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCapTriangleFamily_last.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  exact h.trans (congrArg (fun g => fst (Δ[1] : SSet.{max (u + 1) v w}) (P ⊗ Δ[1]) ≫ g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarAugmentationEdge R C D M Y))
lemma dgGluingNativePreUnitCapTriangleFamily_zero :
    (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫ dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeTransport_endpoint_congr.{max (u + 1) v, max (u + 1) v w} 2 0 _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreUnitCapTriangleFamily_zero.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
lemma dgGluingNativeExitUnitCapTriangleFamily_one :
    (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫ dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeTransport_endpoint_congr.{max (u + 1) v, max (u + 1) v w} 2 1 _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCapTriangleFamily_one.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
lemma dgGluingNativePreUnitCapTriangleFamily_one_projection :
    (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫ dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ P) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativePreUnitCapTriangleFamily_reindex, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCapFamily_one]
lemma dgGluingNativeExitUnitCapTriangleFamily_zero_projection :
    (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫ dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] ⊗ P) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeExitUnitCapTriangleFamily_reindex, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCapFamily_zero]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
