module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCanonicalIntervalNormalization
/-! # 六片の係数対角と正本正規化 prism の全区間面

概要：係数片の対角を、同じ正規化 prism の導来区間族へ厳密に接続する。
方針：四面体の長辺を後正規化面へ制限し、二つの区間因子の交換を相殺する。
規約：元 Hom 入力・全区間・正規化 prism を変更しない。
使われ方：六片の高次合成関係を、正本係数 path の両端固定比較へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
lemma dgGluingPrismIntervalSquare_swap {K L Z : SSet.{u}}
    (h : (Δ[1] : SSet.{u}) ⊗ K ⟶ L) (e : (Δ[1] : SSet.{u}) ⊗ L ⟶ Z) :
    dgGluingPrismParameterReindex (β_ (Δ[1] : SSet.{u}) Δ[1]).hom K ≫
        dgGluingPrismIntervalSquare h e = (Δ[1] ◁ h) ≫ e := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

lemma dgGluingNativeNormalizationAugmentationTetrahedron_normalized_edge :
    (Δ[1] ◁ ((stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4)) ▷ P)) ≫
        dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 P)) ≫
        dgGluingNativeDerivedPostNormalizeCube R C D M X Y := by
  rw [comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    dgGluingNativeNormalizationAugmentationTetrahedron_one R C D M X Y,
    dgGluingNativeAugmentationTriangle_post_normalized R C D M X Y]

lemma dgGluingNativeUnitCapPastingTriangleFamily_coefficient_diagonal :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 4 =
      (Δ[1] ◁ dgGluingNativeModuleNormalizedPrism R C D M X Y) ≫
        (dgGluingNativeModuleNormalizedIntervalEvaluation R C D M X Y ≫
          dgGluingUniverseModuleDerivedComparison.{u, v, w} R C) := by
  rw [dgGluingNativeUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_coefficient_diagonal]
  simp only [Category.assoc]
  rw [dgGluingNativeNormalizationAugmentationTetrahedron_normalized_edge R C D M X Y,
    dgGluingNativeDerivedPostNormalizeCube_interval_face R C D M X Y,
    dgGluingPrismIntervalSquare_swap]

lemma dgGluingNativeModuleNormalizedIntervalEvaluation_derived :
    dgGluingNativeModuleNormalizedIntervalEvaluation R C D M X Y ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C =
      intervalMappingUncurry
        ((uliftPinchedHomIso.{max (u + 1) v, max (u + 1) v w}
          (C := dgNerve R (RightModule R C))
          (Simplex.vertex (representable R X.left)) (Simplex.vertex (M.rightAt Y.right))).hom ≫
        pinchedHomMap (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
          (ULift.up (Simplex.vertex (representable R X.left)))
          (ULift.up (Simplex.vertex (M.rightAt Y.right))) ≫
        pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingNativeModuleNormalizedIntervalEvaluation,
    dgGluingNativeModulePinchedIntervalEvaluation, dgGluingUliftPinchedInterval_uncurry,
    ← dgGluingPinchedInterval_postcomp]
  simp only [Category.assoc]

lemma dgGluingNativeDerivedNormalizedIntervalPrism_canonical_evaluate :
    intervalMappingUncurry (dgGluingNativeDerivedNormalizedIntervalPrism R C D M X Y) =
      intervalMappingUncurry ((Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        dgGluingHomDerivedAugmentationPrism R C D M X Y ≫
          pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingNativeDerivedNormalizedIntervalPrism_factor,
    dgGluingHomDerivedAugmentationIntervalPrism]
  have he := dgGluingPinchedIntervalEndpointTransport_uncurry
    (dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C X.left).symm
    (dgGluingUniverseDerivedCoefficient_vertex R C D M Y.right).symm
    ((Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
      dgGluingHomDerivedAugmentationPrism R C D M X Y)
  simpa only [Category.assoc, dgGluingDerivedCoefficientEndpointIso] using he

lemma dgGluingNativeUnitCapIntervalTriangle_coefficient_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ dgGluingNativeUnitCapIntervalTriangle R C D M X Y 4 =
      (Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        dgGluingHomDerivedAugmentationPrism R C D M X Y ≫
          pinchedHomToIntervalMappingSpace _ _ := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, dgGluingNativeUnitCapIntervalTriangle_evaluate,
    dgGluingNativeUnitCapPastingTriangleFamily_coefficient_diagonal R C D M X Y,
    dgGluingNativeModuleNormalizedIntervalEvaluation_derived R C D M X Y]
  calc
    _ = intervalMappingUncurry
        (dgGluingNativeDerivedNormalizedIntervalPrism R C D M X Y) := by
      simp only [dgGluingNativeDerivedNormalizedIntervalPrism,
        intervalMappingUncurry_precomp]
    _ = _ := dgGluingNativeDerivedNormalizedIntervalPrism_canonical_evaluate R C D M X Y
end SerrePositivity.InfinityCategories
