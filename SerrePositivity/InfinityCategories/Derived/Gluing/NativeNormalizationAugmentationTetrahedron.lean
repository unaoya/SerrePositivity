module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationCompositionTetrahedron

/-! # 正規化四面体上の native 導来 augmentation

概要：前後の標準合成三角形を同時に保つ四面体へ、実導来 augmentation を適用する。
方針：元の四面体全体を共通宇宙へ写し、同じ導来加群関手で後合成する。
規約：指定面と元 Hom 入力を厳密に回収し、側面を省略しない。
使われ方：共有面・側面を含む相対二次元比較の実高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "E" => RightModule R C
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

/-- 概要：元加群の正規化四面体へ augmentation 全区間族を適用する。
方針：対象の宇宙輸送を元に戻すまでを一つの実射にする。
規約：元の全四面体を保持する。使われ方：native 正規化四面体の実入力。 -/
def dgGluingNativeNormalizationRawTetrahedron :=
  (Δ[1] ◁ dgGluingNormalizationCompositionTetrahedron R E IX IY (𝟙 _)) ≫
    dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

/-- 概要：実導来加群上の正規化四面体と全 augmentation。
方針：標準単体上の区間族の輸送を四面体に適用する。
規約：元 Hom 入力を変えない。使われ方：③の側面を含む相対比較。 -/
def dgGluingNativeNormalizationAugmentationTetrahedron :=
  dgGluingNativeNormalizationSimplexPrism R C D M X Y 3
    (dgGluingNativeNormalizationRawTetrahedron R C D M X Y)

lemma dgGluingNativeNormalizationRawTetrahedron_one :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 4) ▷ _)) ≫
        dgGluingNativeNormalizationRawTetrahedron R C D M X Y =
      dgGluingNativePostNormalizeRawTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationRawTetrahedron, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNormalizationCompositionTetrahedron_one]
  rfl

lemma dgGluingNativeNormalizationRawTetrahedron_three :
    (Δ[1] ◁ (stdSimplex.δ (3 : Fin 4) ▷ _)) ≫
        dgGluingNativeNormalizationRawTetrahedron R C D M X Y =
      dgGluingNativePreNormalizeRawTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationRawTetrahedron, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNormalizationCompositionTetrahedron_three]
  rfl

lemma dgGluingNativeNormalizationAugmentationTetrahedron_one :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 4) ▷ P)) ≫
        dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
      dgGluingNativePostNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationAugmentationTetrahedron,
    dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeNormalizationRawTetrahedron_one]
  rfl

lemma dgGluingNativeNormalizationAugmentationTetrahedron_three :
    (Δ[1] ◁ (stdSimplex.δ (3 : Fin 4) ▷ P)) ≫
        dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
      dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationAugmentationTetrahedron,
    dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeNormalizationRawTetrahedron_three]
  rfl

end SerrePositivity.InfinityCategories
