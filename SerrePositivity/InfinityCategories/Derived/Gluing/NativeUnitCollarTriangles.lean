module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseTriangleTimeFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.PreNormalizeFirstCompositionPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.PostNormalizeLastCompositionPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowComposition
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CartesianMonoidalCategory DGNerve SSet
open HomotopyLimits
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativePreNormalizeUnitCollarTriangleFamily :=
  (Δ[2] ◁ (dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
    dgGluingUliftTriangleTimeFamily.{max (u+1) v, max (u+1) v w} 2
      (dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _)) ≫
      dgGluingUniverseModuleDerivedComparison.{u,v,w} R C
lemma dgGluingNativePreNormalizeUnitCollarTriangleFamily_reindex :
    dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y =
    dgGluingTriangleTimeReindex dgGluingFirstUnitCollar ≫
      dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativePreNormalizeUnitCollarTriangleFamily]
  have hraw : dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _) =
      dgGluingTriangleTimeReindex dgGluingFirstUnitCollar ≫
        dgGluingNativePreNormalizeRawTriangle R C D M X Y := rfl
  rw [hraw, dgGluingUliftTriangleTimeFamily_first_reindex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingNativeUnitCollarAugmentationEdge :
    (uliftStdSimplexIso.{max (u+1) v, max (u+1) v w} 1).inv ≫
      (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).map
        ((SSet.yonedaEquiv (X := dgNerve R RM)).symm (dgClosedEdge R RM (IX).augmentation).edge) ≫
      dgGluingUniverseModuleDerivedComparison.{u,v,w} R C =
    SSet.yonedaEquiv.symm (dgGluingDerivedAugmentationEdge R C D M X).edge := by
  have h : (uliftStdSimplexIso.{max (u+1) v, max (u+1) v w} 1).inv ≫
      (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).map
        ((SSet.yonedaEquiv (X := dgNerve R RM)).symm (dgClosedEdge R RM (IX).augmentation).edge) =
      (SSet.yonedaEquiv (X := (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).obj
        (dgNerve R RM))).symm (ULift.up (dgClosedEdge R RM (IX).augmentation).edge) := by
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
        SSet.yonedaEquiv.symm (dgGluingDerivedAugmentationEdge R C D M X).edge := by
  let V := dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _)
  let e := (SSet.yonedaEquiv (X := dgNerve R RM)).symm
    (dgClosedEdge R RM (IX).augmentation).edge
  let K₀ := DGNerve.pinchedHom R
    (DGFunctorCommaObject R RM RM (DGFunctor.id RM)) IX IY
  have hU := dgGluingUliftTriangleTimeFamily_fixed_edge.{max (u+1) v, max (u+1) v w}
    2 V e (dgGluingPreNormalizeUnitCollarTriangleFamily_first.{u, max (u+1) v}
      R RM IX IY (𝟙 _))
  calc
    _ = (Δ[1] ◁ (dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
        ((stdSimplex.δ (2 : Fin 3) ▷
          ((SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).obj K₀ ⊗ Δ[1])) ≫
          dgGluingUliftTriangleTimeFamily.{max (u+1) v, max (u+1) v w} 2 V) ≫
            dgGluingUniverseModuleDerivedComparison.{u,v,w} R C := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = (Δ[1] ◁ (dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
        (fst (Δ[1] : SSet.{max (u+1) v w})
          ((SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).obj K₀ ⊗ Δ[1]) ≫
          (uliftStdSimplexIso.{max (u+1) v, max (u+1) v w} 1).inv ≫
          (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).map e) ≫
            dgGluingUniverseModuleDerivedComparison.{u,v,w} R C := by rw [hU]
    _ = fst (Δ[1] : SSet.{max (u+1) v w}) (P ⊗ Δ[1]) ≫
        ((uliftStdSimplexIso.{max (u+1) v, max (u+1) v w} 1).inv ≫
          (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).map e ≫
            dgGluingUniverseModuleDerivedComparison.{u,v,w} R C) := by
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
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        (dgGluingLaxHomArrowTriangles R C D M X Y).first := by
  have hs : squareTriangle (1 : Fin 2) =
      squareTriangle (0 : Fin 2) ≫ (β_ (Δ[1] : SSet.{max (u+1) v w}) Δ[1]).hom := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext
    all_goals apply SSet.stdSimplex.ext
    all_goals intro j; fin_cases j <;> rfl
  calc
    _ = (squareTriangle 1 ▷ P) ≫ (α_ (Δ[1] : SSet.{max (u+1) v w}) Δ[1] P).hom ≫
        ((Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
          dgGluingNativePreNormalizeAugmentationTriangle R C D M X Y) := by
      rw [dgGluingNativePreNormalizeUnitCollarTriangleFamily_reindex,
        ← Category.assoc, dgGluingFirstUnitCollarFamily_one]
      simp only [Category.assoc]
    _ = dgGluingNativeNormalizationFirstTriangle R C D M X Y := by
      rw [dgGluingNativeAugmentationTriangle_pre_original, hs, comp_whiskerRight]
      simp only [dgGluingNativeNormalizationFirstTriangle,
        dgGluingNativeNormalizationArrowSquare, Category.assoc]
    _ = _ := dgGluingNativeNormalizationFirstTriangle_eq R C D M X Y
def dgGluingNativePostNormalizeUnitCollarTriangleFamily :=
  (Δ[2] ◁ (dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
    dgGluingUliftTriangleTimeFamily.{max (u+1) v, max (u+1) v w} 2
      (dgGluingPostNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _)) ≫
      dgGluingUniverseModuleDerivedComparison.{u,v,w} R C
lemma dgGluingNativePostNormalizeUnitCollarTriangleFamily_reindex :
    dgGluingNativePostNormalizeUnitCollarTriangleFamily R C D M X Y =
    dgGluingTriangleTimeReindex dgGluingLastUnitCollar ≫
      dgGluingNativePostNormalizeAugmentationTriangle R C D M X Y := by
  rw [dgGluingNativePostNormalizeUnitCollarTriangleFamily]
  have hraw : dgGluingPostNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _) =
      dgGluingTriangleTimeReindex dgGluingLastUnitCollar ≫
        dgGluingNativePostNormalizeRawTriangle R C D M X Y := rfl
  rw [hraw, dgGluingUliftTriangleTimeFamily_last_reindex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingNativePostNormalizeUnitCollarTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingNativePostNormalizeUnitCollarTriangleFamily R C D M X Y =
      fst (Δ[1] : SSet.{max (u+1) v w}) (P ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (dgGluingDerivedAugmentationEdge R C D M Y).edge := by
  let V := dgGluingPostNormalizeUnitCollarTriangleFamily.{u, max (u+1) v} R RM IX IY (𝟙 _)
  let e := (SSet.yonedaEquiv (X := dgNerve R RM)).symm
    (dgClosedEdge R RM (IY).augmentation).edge
  let K₀ := DGNerve.pinchedHom R
    (DGFunctorCommaObject R RM RM (DGFunctor.id RM)) IX IY
  have hU := dgGluingUliftTriangleTimeFamily_fixed_edge.{max (u+1) v, max (u+1) v w}
    0 V e (dgGluingPostNormalizeUnitCollarTriangleFamily_last.{u, max (u+1) v}
      R RM IX IY (𝟙 _))
  calc
    _ = (Δ[1] ◁ (dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
        ((stdSimplex.δ (0 : Fin 3) ▷
          ((SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).obj K₀ ⊗ Δ[1])) ≫
          dgGluingUliftTriangleTimeFamily.{max (u+1) v, max (u+1) v w} 2 V) ≫
            dgGluingUniverseModuleDerivedComparison.{u,v,w} R C := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = (Δ[1] ◁ (dgGluingNativeNormalizationHomInput R C D M X Y ▷ Δ[1])) ≫
        (fst (Δ[1] : SSet.{max (u+1) v w})
          ((SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).obj K₀ ⊗ Δ[1]) ≫
          (uliftStdSimplexIso.{max (u+1) v, max (u+1) v w} 1).inv ≫
          (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).map e) ≫
            dgGluingUniverseModuleDerivedComparison.{u,v,w} R C := by rw [hU]
    _ = fst (Δ[1] : SSet.{max (u+1) v w}) (P ⊗ Δ[1]) ≫
        ((uliftStdSimplexIso.{max (u+1) v, max (u+1) v w} 1).inv ≫
          (SSet.uliftFunctor.{max (u+1) v w, max (u+1) v}).map e ≫
            dgGluingUniverseModuleDerivedComparison.{u,v,w} R C) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := congrArg (fun g => fst (Δ[1] : SSet.{max (u+1) v w}) (P ⊗ Δ[1]) ≫ g)
      (dgGluingNativeUnitCollarAugmentationEdge R C D M Y)


end SerrePositivity.InfinityCategories
