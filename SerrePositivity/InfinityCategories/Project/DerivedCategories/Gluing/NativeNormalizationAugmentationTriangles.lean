module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeNormalizationPasting
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseSimplexPrismFamilies

/-! # native 正規化の標準合成三角形と全 augmentation

概要：元加群の標準合成三角形を共通宇宙と正本導来加群へ移す。
方針：全区間・全二単体族を輸送し、元の Hom 入力で制限する。
規約：Small は元 C にだけ仮定し、加群圏には仮定しない。
使われ方：前後の三角形 prism を側面ごと相対貼り合わせへ供給する。
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
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M Y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y

/-- 概要：実加群の前正規化の標準合成三角形を保持する。
方針：元 augmentation の後で対象宇宙だけを戻す。
規約：全 Hom 入力上の実射。使われ方：共通宇宙への前 prism の入力。 -/
def dgGluingNativePreNormalizeRawTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeAugmentationTriangle R E IX IY (𝟙 _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

/-- 概要：実加群の後正規化の標準合成三角形を保持する。
方針：元 augmentation の後で対象宇宙だけを戻す。
規約：全 Hom 入力上の実射。使われ方：共通宇宙への後 prism の入力。 -/
def dgGluingNativePostNormalizeRawTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle R E IX IY (𝟙 _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

/-- 概要：標準単体上の区間族を元 Hom 入力と正本導来関手へ移す。
方針：二つの単体因子を共通宇宙へ移し、元入力で前合成する。
規約：元加群を置き換えない。使われ方：native augmentation の三角形 prism。 -/
def dgGluingNativeNormalizationSimplexPrism (n : ℕ)
    (V : (Δ[1] : SSet.{max (u + 1) v}) ⊗
      (Δ[n] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Q IX IY) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) :=
  (Δ[1] ◁ (Δ[n] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexPrismFamily.{max (u + 1) v, max (u + 1) v w} n V ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C

/-- 概要：前正規化三角形に沿う実導来 augmentation の全族。
方針：元の三角形 prism を同じ正本関手で写す。
規約：共有面・始側面を保持する。使われ方：③の相対貼り合わせ。 -/
def dgGluingNativePreNormalizeAugmentationTriangle :=
  dgGluingNativeNormalizationSimplexPrism R C D M X Y 2
    (dgGluingNativePreNormalizeRawTriangle R C D M X Y)

/-- 概要：後正規化三角形に沿う実導来 augmentation の全族。
方針：元の三角形 prism を同じ正本関手で写す。
規約：共有面・係数面・終側面を保持する。使われ方：③の相対貼り合わせ。 -/
def dgGluingNativePostNormalizeAugmentationTriangle :=
  dgGluingNativeNormalizationSimplexPrism R C D M X Y 2
    (dgGluingNativePostNormalizeRawTriangle R C D M X Y)

lemma dgGluingNativeNormalizationSimplexPrism_face {n : ℕ}
    (V : (Δ[1] : SSet.{max (u + 1) v}) ⊗
      (Δ[n + 1] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Q IX IY) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (i : Fin (n + 2)) :
    (Δ[1] ◁ (stdSimplex.δ i ▷ P)) ≫
        dgGluingNativeNormalizationSimplexPrism R C D M X Y (n + 1) V =
      dgGluingNativeNormalizationSimplexPrism R C D M X Y n
        ((Δ[1] ◁ (stdSimplex.δ i ▷ _)) ≫ V) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingNativeNormalizationSimplexPrism_square
    (V : (Δ[1] : SSet.{max (u + 1) v}) ⊗
      (Δ[1] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Q IX IY) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) :
    dgGluingNativeNormalizationSimplexPrism R C D M X Y 1 V =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{max (u + 1) v, max (u + 1) v w} V ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C := rfl

lemma dgGluingNativeAugmentationTriangle_raw_pre_original :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ _)) ≫
        dgGluingNativePreNormalizeRawTriangle R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawCube R C D M X Y := by
  have he := congrArg (fun z => z ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationTriangle_cube_pre_original R E IX IY (𝟙 _))
  simpa only [dgGluingNativePreNormalizeRawTriangle,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawCube, Category.assoc] using he

lemma dgGluingNativeAugmentationTriangle_pre_original :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 P)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube R C D M X Y := by
  rw [dgGluingNativePreNormalizeAugmentationTriangle,
    dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeAugmentationTriangle_raw_pre_original,
    dgGluingNativeNormalizationSimplexPrism_square,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube_inner]

lemma dgGluingNativeAugmentationTriangle_raw_pre_shared :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ _)) ≫
        dgGluingNativePreNormalizeRawTriangle R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawCube R C D M X Y := by
  have he := congrArg (fun z => z ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationTriangle_cube_pre_shared R E IX IY (𝟙 _))
  simpa only [dgGluingNativePreNormalizeRawTriangle,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawCube, Category.assoc] using he

lemma dgGluingNativeAugmentationTriangle_pre_shared :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube R C D M X Y := by
  rw [dgGluingNativePreNormalizeAugmentationTriangle,
    dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeAugmentationTriangle_raw_pre_shared,
    dgGluingNativeNormalizationSimplexPrism_square,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube_inner]

lemma dgGluingNativeAugmentationTriangle_raw_post_normalized :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ _)) ≫
        dgGluingNativePostNormalizeRawTriangle R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePostNormalizeRawCube R C D M X Y := by
  have he := congrArg (fun z => z ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationTriangle_cube_post_normalized R E IX IY (𝟙 _))
  simpa only [dgGluingNativePostNormalizeRawTriangle,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePostNormalizeRawCube, Category.assoc] using he

lemma dgGluingNativeAugmentationTriangle_post_normalized :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingNativePostNormalizeAugmentationTriangle R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPostNormalizeCube R C D M X Y := by
  rw [dgGluingNativePostNormalizeAugmentationTriangle,
    dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeAugmentationTriangle_raw_post_normalized,
    dgGluingNativeNormalizationSimplexPrism_square,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPostNormalizeCube_inner]

lemma dgGluingNativeAugmentationTriangle_raw_post_side :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ _)) ≫
        dgGluingNativePostNormalizeRawTriangle R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePostNormalizeRawCube R C D M X Y := by
  have he := congrArg (fun z => z ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationTriangle_cube_post_side R E IX IY (𝟙 _))
  simpa only [dgGluingNativePostNormalizeRawTriangle,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePostNormalizeRawCube, Category.assoc] using he

lemma dgGluingNativeAugmentationTriangle_post_side :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingNativePostNormalizeAugmentationTriangle R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 P)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPostNormalizeCube R C D M X Y := by
  rw [dgGluingNativePostNormalizeAugmentationTriangle,
    dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeAugmentationTriangle_raw_post_side,
    dgGluingNativeNormalizationSimplexPrism_square,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPostNormalizeCube_inner]

lemma dgGluingNativeAugmentationTriangles_shared :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingNativePostNormalizeAugmentationTriangle R C D M X Y =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativePostNormalizeAugmentationTriangle,
    dgGluingNativePreNormalizeAugmentationTriangle,
    dgGluingNativeNormalizationSimplexPrism_face,
    dgGluingNativeNormalizationSimplexPrism_face]
  apply congrArg (dgGluingNativeNormalizationSimplexPrism R C D M X Y 1)
  have he := congrArg (fun z => z ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle_shared R E IX IY (𝟙 _))
  simpa only [dgGluingNativePostNormalizeRawTriangle,
    dgGluingNativePreNormalizeRawTriangle, Category.assoc] using he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
