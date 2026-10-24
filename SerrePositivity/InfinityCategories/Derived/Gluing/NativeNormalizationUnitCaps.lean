module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeExitUnitCollarTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationUnitCaps
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseUnitCapFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.TriangleTimeTransport
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CartesianMonoidalCategory DGNerve SSet
open HomotopyLimits
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativePreUnitCapTriangleFamily :=
  dgGluingTriangleTimeTransport.{max (u + 1) v, max (u + 1) v w} 2
  (dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
  (dgGluingNativeNormalizationHomInput R C D M X Y)
  (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
def dgGluingNativeExitUnitCapTriangleFamily :=
  dgGluingTriangleTimeTransport.{max (u + 1) v, max (u + 1) v w} 2
  (dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
  (dgGluingNativeNormalizationHomInput R C D M X Y)
  (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
lemma dgGluingNativePreUnitCapTriangleFamily_reindex :
    dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
    dgGluingTriangleTimeReindex dgGluingFirstUnitCap ≫
      dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativePreUnitCapTriangleFamily, dgGluingTriangleTimeTransport]
  have hraw : dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _) =
      dgGluingTriangleTimeReindex dgGluingFirstUnitCap ≫
        dgGluingNativePreNormalizeRawTriangle R C D M X Y := rfl
  rw [hraw, dgGluingUliftTriangleTimeFamily_first_cap_reindex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingNativeExitUnitCapTriangleFamily_reindex :
    dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
    dgGluingTriangleTimeReindex dgGluingLastUnitCap ≫
      dgGluingNativeExitAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeExitUnitCapTriangleFamily, dgGluingTriangleTimeTransport]
  have hraw : dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _) =
      dgGluingTriangleTimeReindex dgGluingLastUnitCap ≫
        dgGluingNativeExitAugmentationRawTriangle R C D M X Y := rfl
  rw [hraw, dgGluingUliftTriangleTimeFamily_last_cap_reindex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingNativePreUnitCapTriangleFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (P ⊗ Δ[1])) ≫ dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      fst (Δ[1] : SSet.{max (u + 1) v w}) (P ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (dgGluingDerivedAugmentationEdge R C D M X).edge := by
  have h :=
  dgGluingTriangleTimeTransport_fixed_edge.{max (u + 1) v, max (u + 1) v w} 2
    (dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    ((SSet.yonedaEquiv (X := dgNerve R RM)).symm (dgClosedEdge R RM (IX).augmentation).edge)
    (dgGluingPreUnitCapTriangleFamily_first.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  exact h.trans (congrArg (fun g => fst (Δ[1] : SSet.{max (u + 1) v w}) (P ⊗ Δ[1]) ≫ g)
    (dgGluingNativeUnitCollarAugmentationEdge R C D M X))
lemma dgGluingNativeExitUnitCapTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (P ⊗ Δ[1])) ≫ dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      fst (Δ[1] : SSet.{max (u + 1) v w}) (P ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (dgGluingDerivedAugmentationEdge R C D M Y).edge := by
  have h :=
  dgGluingTriangleTimeTransport_fixed_edge.{max (u + 1) v, max (u + 1) v w} 0
    (dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    ((SSet.yonedaEquiv (X := dgNerve R RM)).symm (dgClosedEdge R RM (IY).augmentation).edge)
    (dgGluingExitUnitCapTriangleFamily_last.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  exact h.trans (congrArg (fun g => fst (Δ[1] : SSet.{max (u + 1) v w}) (P ⊗ Δ[1]) ≫ g)
    (dgGluingNativeUnitCollarAugmentationEdge R C D M Y))
lemma dgGluingNativePreUnitCapTriangleFamily_zero :
    (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫ dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫ dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y :=
  dgGluingTriangleTimeTransport_endpoint_congr.{max (u + 1) v, max (u + 1) v w} 2 0 _ _
    (dgGluingPreUnitCapTriangleFamily_zero.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
lemma dgGluingNativeExitUnitCapTriangleFamily_one :
    (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫ dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫ dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y :=
  dgGluingTriangleTimeTransport_endpoint_congr.{max (u + 1) v, max (u + 1) v w} 2 1 _ _
    (dgGluingExitUnitCapTriangleFamily_one.{u, max (u + 1) v} R RM IX IY (𝟙 _))
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
lemma dgGluingNativePreUnitCapTriangleFamily_one_projection :
    (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫ dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      prismEndpoint 1 (Δ[2] ⊗ P) ≫
        dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativePreUnitCapTriangleFamily_reindex, ← Category.assoc,
    dgGluingFirstUnitCapFamily_one]
lemma dgGluingNativeExitUnitCapTriangleFamily_zero_projection :
    (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫ dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      prismEndpoint 0 (Δ[2] ⊗ P) ≫ dgGluingNativeExitAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeExitUnitCapTriangleFamily_reindex, ← Category.assoc,
    dgGluingLastUnitCapFamily_zero]
end SerrePositivity.InfinityCategories
