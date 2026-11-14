module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.NativeNormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.NormalizationCompositionTetrahedron

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "E" => _root_.SerrePositivity.DifferentialGraded.RightModule R C
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M Y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y

/-- 概要：元加群の正規化四面体へ augmentation 全区間族を適用する。
方針：対象の宇宙輸送を元に戻すまでを一つの実射にする。
規約：元の全四面体を保持する。使われ方：native 正規化四面体の実入力。 -/
def dgGluingNativeNormalizationRawTetrahedron :=
  (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationCompositionTetrahedron R E IX IY (𝟙 _)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

/-- 概要：実導来加群上の正規化四面体と全 augmentation。
方針：標準単体上の区間族の輸送を四面体に適用する。
規約：元 Hom 入力を変えない。使われ方：③の側面を含む相対比較。 -/
def dgGluingNativeNormalizationAugmentationTetrahedron :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism R C D M X Y 3
    (dgGluingNativeNormalizationRawTetrahedron R C D M X Y)

/-- 概要：元 Hom と終閉射の標準側面上の全 augmentation。
方針：四面体の指定第零面を元加群へ戻す。
規約：元入力と標準合成面を保持する。使われ方：終側面の導来整合性。 -/
def dgGluingNativeNormalizationExitRawTriangle :=
  (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationExitTriangle R E IX IY (𝟙 _)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

/-- 概要：残る始側面上の全 augmentation。
方針：同じ四面体の第二面を元加群へ戻す。
規約：新しい面を選ばない。使われ方：始側面の導来整合性。 -/
def dgGluingNativeNormalizationEntranceRawTriangle :=
  (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationEntranceTriangle R E IX IY (𝟙 _)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

def dgGluingNativeNormalizationExitAugmentationTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism R C D M X Y 2
    (dgGluingNativeNormalizationExitRawTriangle R C D M X Y)

def dgGluingNativeNormalizationEntranceAugmentationTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism R C D M X Y 2
    (dgGluingNativeNormalizationEntranceRawTriangle R C D M X Y)

lemma dgGluingNativeNormalizationRawTetrahedron_zero :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 4) ▷ _)) ≫
        dgGluingNativeNormalizationRawTetrahedron R C D M X Y =
      dgGluingNativeNormalizationExitRawTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationRawTetrahedron, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationCompositionTetrahedron_zero]
  rfl

lemma dgGluingNativeNormalizationRawTetrahedron_two :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 4) ▷ _)) ≫
        dgGluingNativeNormalizationRawTetrahedron R C D M X Y =
      dgGluingNativeNormalizationEntranceRawTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationRawTetrahedron, ← Category.assoc, ← whiskerLeft_comp]
  rfl

lemma dgGluingNativeNormalizationRawTetrahedron_one :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 4) ▷ _)) ≫
        dgGluingNativeNormalizationRawTetrahedron R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePostNormalizeRawTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationRawTetrahedron, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationCompositionTetrahedron_one]
  rfl

lemma dgGluingNativeNormalizationRawTetrahedron_three :
    (Δ[1] ◁ (stdSimplex.δ (3 : Fin 4) ▷ _)) ≫
        dgGluingNativeNormalizationRawTetrahedron R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationRawTetrahedron, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationCompositionTetrahedron_three]
  rfl

lemma dgGluingNativeNormalizationAugmentationTetrahedron_one :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 4) ▷ P)) ≫
        dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePostNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationAugmentationTetrahedron,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeNormalizationRawTetrahedron_one]
  rfl

lemma dgGluingNativeNormalizationAugmentationTetrahedron_three :
    (Δ[1] ◁ (stdSimplex.δ (3 : Fin 4) ▷ P)) ≫
        dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationAugmentationTetrahedron,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeNormalizationRawTetrahedron_three]
  rfl

lemma dgGluingNativeNormalizationAugmentationTetrahedron_zero :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 4) ▷ P)) ≫
        dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
      dgGluingNativeNormalizationExitAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationAugmentationTetrahedron,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeNormalizationRawTetrahedron_zero]
  rfl

lemma dgGluingNativeNormalizationAugmentationTetrahedron_two :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 4) ▷ P)) ≫
        dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
      dgGluingNativeNormalizationEntranceAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeNormalizationAugmentationTetrahedron,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeNormalizationRawTetrahedron_two]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
