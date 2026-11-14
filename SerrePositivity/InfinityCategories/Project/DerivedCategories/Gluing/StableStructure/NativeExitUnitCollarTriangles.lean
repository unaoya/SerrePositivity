module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.NativeUnitCollarTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.ExitLastCompositionPath
/-! # native 標準終側合成面の元終辺固定補正

概要：同じ四面体の終側合成面から、正本の第二三角形を元端に持つ補正族を作る。
方針：元 Hom 入力と単位補正を共通宇宙へ移し、元 augmentation 辺を厳密に回収する。
規約：正本の元第二三角形と全パラメーターを保持する。
使われ方：第一補正族と同じ元対角を持つ第二変形を、相対二次元比較へ供給する。
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

def dgGluingNativeExitAugmentationRawTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitAugmentationTriangle.{u, max (u+1) v} R RM IX IY (𝟙 _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u+1) v, max (u+1) v} R RM)
def dgGluingNativeExitAugmentationTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism R C D M X Y 2
    (dgGluingNativeExitAugmentationRawTriangle R C D M X Y)
def dgGluingNativeExitUnitCollarTriangleFamily :=
  (Δ[2] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily.{max (u+1) v, max (u+1) v w} 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u,v,w} R C
lemma dgGluingNativeExitUnitCollarTriangleFamily_reindex :
    dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar ≫
      dgGluingNativeExitAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativeExitUnitCollarTriangleFamily]
  have hraw : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar ≫
        dgGluingNativeExitAugmentationRawTriangle R C D M X Y := rfl
  rw [hraw, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_last_reindex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingNativeExitUnitCollarTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y =
      fst (Δ[1] : SSet.{max (u+1) v w}) (P ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y).edge := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _)
  let e := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R RM)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R RM (IY).augmentation).edge
  let K₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R RM RM (DGFunctor.id RM)) IX IY
  have hU := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_fixed_edge.{max (u+1) v, max (u+1) v w}
    0 V e (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily_last.{u, max (u+1) v}
      R RM IX IY (𝟙 _))
  calc
    _ = (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
        ((stdSimplex.δ (0 : Fin 3) ▷
          ((SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).obj K₀ ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily.{max (u+1) v, max (u+1) v w} 2 V) ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u,v,w} R C := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
        (fst (Δ[1] : SSet.{max (u+1) v w})
          ((SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).obj K₀ ⊗ Δ[1]) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{max (u+1) v, max (u+1) v w} 1).inv ≫
          (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).map e) ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u,v,w} R C := by rw [hU]
    _ = fst (Δ[1] : SSet.{max (u+1) v w}) (P ⊗ Δ[1]) ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{max (u+1) v, max (u+1) v w} 1).inv ≫
          (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).map e ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u,v,w} R C) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := congrArg (fun g => fst (Δ[1] : SSet.{max (u+1) v w}) (P ⊗ Δ[1]) ≫ g)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarAugmentationEdge R C D M Y)





lemma dgGluingNativeExitAugmentationTriangle_original :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
      dgGluingNativeExitAugmentationTriangle R C D M X Y =
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y := by
  have h0 := congrArg (fun g => g ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u+1) v, max (u+1) v} R RM))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitAugmentationTriangle_original.{u, max (u+1) v} R RM IX IY (𝟙 _))
  have h1 := congrArg (fun g => g ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u+1) v, max (u+1) v} R RM))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeAugmentationTriangle_original R RM IX IY (𝟙 _))
  have hr : (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ _)) ≫
      dgGluingNativeExitAugmentationRawTriangle R C D M X Y =
      (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ _)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawTriangle R C D M X Y := by
    simpa only [dgGluingNativeExitAugmentationRawTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawTriangle,
      Category.assoc] using h0.trans h1.symm
  rw [dgGluingNativeExitAugmentationTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeAugmentationTriangle,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism_face, hr]
lemma dgGluingNativeExitUnitCollarTriangleFamily_zero :
    (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫ dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y =
      (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowTriangles R C D M X Y).second := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (0 : Fin 2) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (1 : Fin 2) ≫ (β_ (Δ[1] : SSet.{max (u+1) v w}) Δ[1]).hom := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext
    all_goals apply SSet.stdSimplex.ext
    all_goals intro j; fin_cases j <;> rfl
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ P) ≫ (α_ (Δ[1] : SSet.{max (u+1) v w}) Δ[1] P).hom ≫
        ((Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
          dgGluingNativeExitAugmentationTriangle R C D M X Y) := by
      rw [dgGluingNativeExitUnitCollarTriangleFamily_reindex, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollarFamily_zero]
      simp only [Category.assoc]
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationLastTriangle R C D M X Y := by
      rw [dgGluingNativeExitAugmentationTriangle_original,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeAugmentationTriangle_pre_original, hs, comp_whiskerRight]
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationLastTriangle,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationArrowSquare, Category.assoc]
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationLastTriangle_eq R C D M X Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
