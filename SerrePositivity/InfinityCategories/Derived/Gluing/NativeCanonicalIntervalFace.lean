module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCanonicalCoefficientPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationIntervalFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrismIntervalSquareTarget
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniversePinchedIntervalEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTrianglePost

/-! # 実後 cube の canonical 係数区間面

概要：正規化した実後 cube の区間面を canonical 導来係数の同じ区間評価へ移す。
方針：始域同型の実逆と区間評価の自然性を使い、全 prism の係数表示を代入する。
規約：二つの時間と元の Hom 入力を保持し、異なる対象宇宙は同型で輸送する。
使われ方：cube の入力固定変形を主係数 path の両端固定正規化へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

/-- 概要：canonical 係数写像を実導来加群の区間へ評価する。
方針：指定端点の同型を戻して pinched Hom を区間へ送る。
規約：元の係数空間を始域とする。使われ方：後 cube 面の共通の評価写像。 -/
def dgGluingCanonicalCoefficientIntervalEvaluation :=
  intervalMappingUncurry
    (dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right ≫
      (dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
        pinchedHomToIntervalMappingSpace _ _)

lemma dgGluingNativeNormalizedIntervalEvaluation_canonical :
    dgGluingNativeModuleNormalizedIntervalEvaluation R C D M X Y ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C =
      (Δ[1] ◁ (dgGluingCanonicalCoefficientDomainIso R C D M X.left Y.right).inv) ≫
        dgGluingCanonicalCoefficientIntervalEvaluation R C D M X Y := by
  rw [dgGluingCanonicalCoefficientIntervalEvaluation, ← intervalMappingUncurry_precomp]
  have he := congrArg
    (fun f => intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace _ _))
    (dgGluingCanonicalCoefficientMappingComparison_universe_action R C D M X.left Y.right)
  simp only [Category.assoc] at he
  rw [he, ← Category.assoc, dgGluingPinchedInterval_postcomp]
  rw [dgGluingNativeModuleNormalizedIntervalEvaluation,
    dgGluingNativeModulePinchedIntervalEvaluation, dgGluingUliftPinchedInterval_uncurry]

lemma dgGluingNativeDerivedPostNormalizeCube_canonical_interval_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 _)) ≫
        dgGluingNativeDerivedPostNormalizeCube R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y)) ≫
        dgGluingPrismIntervalSquare
          (dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
            (dgGluingHomCoefficientAugmentationPrism R C D M X Y))
          (dgGluingCanonicalCoefficientIntervalEvaluation R C D M X Y) := by
  rw [dgGluingNativeDerivedPostNormalizeCube_interval_face,
    dgGluingNativeNormalizedIntervalEvaluation_canonical,
    ← dgGluingPrismIntervalSquare_target,
    dgGluingNativeNormalizedPrism_canonical_coefficient,
    ← dgGluingPrismIntervalSquare_precomp]

end SerrePositivity.InfinityCategories
