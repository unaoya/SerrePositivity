module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.UniverseTriangleTimeFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.PreNormalizeFirstCompositionPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.PostNormalizeLastCompositionPath
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.NativeNormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.LaxPullbacks.LaxHomArrowComposition
/-! # native 正本の元 augmentation を保つ単位補正

概要：実前後正規化の補正三角形族を、元 Hom 入力とともに正本の導来比較へ移す。
方針：時間付き三角形の宇宙輸送を使い、元 augmentation 辺への固定を回収する。
規約：前側の元端を正本第一三角形そのものに同定し、公開比較を置き換えない。
使われ方：実入力固定変形と選択済み二変形の相対比較を構成する。
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

def dgGluingNativePreNormalizeUnitCollarTriangleFamily :=
  (Δ[2] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily.{max (u+1) v, max (u+1) v w} 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u,v,w} R C
lemma dgGluingNativePreNormalizeUnitCollarTriangleFamily_reindex :
    dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativePreNormalizeUnitCollarTriangleFamily]
  have hraw : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawTriangle R C D M X Y := rfl
  rw [hraw, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_first_reindex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingNativeUnitCollarAugmentationEdge :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{max (u+1) v, max (u+1) v w} 1).inv ≫
      (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).map
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R RM)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R RM (IX).augmentation).edge) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u,v,w} R C =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X).edge := by
  have h : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{max (u+1) v, max (u+1) v w} 1).inv ≫
      (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).map
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R RM)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R RM (IX).augmentation).edge) =
      (SSet.yonedaEquiv (X := (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R RM))).symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R RM (IX).augmentation).edge) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, h, SSet.yonedaEquiv_symm_comp]
  rfl


lemma dgGluingNativePreNormalizeUnitCollarTriangleFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y =
      fst (Δ[1] : SSet.{max (u+1) v w}) (P ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X).edge := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _)
  let e := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R RM)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R RM (IX).augmentation).edge
  let K₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R RM RM (DGFunctor.id RM)) IX IY
  have hU := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_fixed_edge.{max (u+1) v, max (u+1) v w}
    2 V e (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily_first.{u, max (u+1) v}
      R RM IX IY (𝟙 _))
  calc
    _ = (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
        ((stdSimplex.δ (2 : Fin 3) ▷
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
      (dgGluingNativeUnitCollarAugmentationEdge R C D M X)


lemma dgGluingNativePreNormalizeUnitCollarTriangleFamily_one :
    (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫
      dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y =
      (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowTriangles R C D M X Y).first := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (1 : Fin 2) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (0 : Fin 2) ≫ (β_ (Δ[1] : SSet.{max (u+1) v w}) Δ[1]).hom := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext
    all_goals apply SSet.stdSimplex.ext
    all_goals intro j; fin_cases j <;> rfl
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ P) ≫ (α_ (Δ[1] : SSet.{max (u+1) v w}) Δ[1] P).hom ≫
        ((Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y) := by
      rw [dgGluingNativePreNormalizeUnitCollarTriangleFamily_reindex,
        ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollarFamily_one]
      simp only [Category.assoc]
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationFirstTriangle R C D M X Y := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeAugmentationTriangle_pre_original, hs, comp_whiskerRight]
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationFirstTriangle,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationArrowSquare, Category.assoc]
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationFirstTriangle_eq R C D M X Y
def dgGluingNativePostNormalizeUnitCollarTriangleFamily :=
  (Δ[2] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily.{max (u+1) v, max (u+1) v w} 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u,v,w} R C
lemma dgGluingNativePostNormalizeUnitCollarTriangleFamily_reindex :
    dgGluingNativePostNormalizeUnitCollarTriangleFamily R C D M X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePostNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativePostNormalizeUnitCollarTriangleFamily]
  have hraw : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePostNormalizeRawTriangle R C D M X Y := rfl
  rw [hraw, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_last_reindex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingNativePostNormalizeUnitCollarTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativePostNormalizeUnitCollarTriangleFamily R C D M X Y =
      fst (Δ[1] : SSet.{max (u+1) v w}) (P ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y).edge := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _)
  let e := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R RM)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R RM (IY).augmentation).edge
  let K₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R RM RM (DGFunctor.id RM)) IX IY
  have hU := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_fixed_edge.{max (u+1) v, max (u+1) v w}
    0 V e (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeUnitCollarTriangleFamily_last.{u, max (u+1) v}
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
      (dgGluingNativeUnitCollarAugmentationEdge R C D M Y)


end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
