module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeCanonicalCoefficientPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeNormalizationIntervalFace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PrismIntervalSquareTarget
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniversePinchedIntervalEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionTrianglePost

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 概要：canonical 係数写像を実導来加群の区間へ評価する。
方針：指定端点の同型を戻して pinched Hom を区間へ送る。
規約：元の係数空間を始域とする。使われ方：後 cube 面の共通の評価写像。 -/
def dgGluingCanonicalCoefficientIntervalEvaluation :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)

lemma dgGluingNativeNormalizedIntervalEvaluation_canonical :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleNormalizedIntervalEvaluation R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C =
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientDomainIso R C D M X.left Y.right).inv) ≫
        dgGluingCanonicalCoefficientIntervalEvaluation R C D M X Y := by
  rw [dgGluingCanonicalCoefficientIntervalEvaluation, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  have he := congrArg
    (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalCoefficientMappingComparison_universe_action R C D M X.left Y.right)
  simp only [Category.assoc] at he
  rw [he, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedInterval_postcomp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleNormalizedIntervalEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModulePinchedIntervalEvaluation, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftPinchedInterval_uncurry]

lemma dgGluingNativeDerivedPostNormalizeCube_canonical_interval_face :
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPostNormalizeCube R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismIntervalSquare
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y))
          (dgGluingCanonicalCoefficientIntervalEvaluation R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPostNormalizeCube_interval_face,
    dgGluingNativeNormalizedIntervalEvaluation_canonical,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismIntervalSquare_target,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedPrism_canonical_coefficient,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismIntervalSquare_precomp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
