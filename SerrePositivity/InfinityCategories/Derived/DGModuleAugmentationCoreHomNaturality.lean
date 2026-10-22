module
public import SerrePositivity.InfinityCategories.Derived.DGModuleRawOutputPrecompHom
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationRawHomNaturality
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationRawFactorCore
public import SerrePositivity.InfinityCategories.Derived.FunctorHomSquareTransport
/-!
概要：元の augmentation の自然性を、二射影と同じ指定入力切断の表示へ移す。
方針：同じ全関手射の端点輸送と二段前合成の整合性を保つ。
規約：指定比較と切断・計算上限を変更しない。使われ方：元の κ の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (E K : Type v)
  [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
local notation "L" => dgModuleResolvedInfinity R (RightModule R K) K
  (DGFunctor.id (RightModule R K))
variable (C : Type (max (u + 1) v)) [DGCategory R C]
  (F : DGFunctor R C (RightModule R E))
local notation "T" => DGModuleFunctorResolutionObject R C E F
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)
local notation "G" => dgModuleFunctorResolutionReplacement R C E F
local notation "P0" => dgModuleFunctorResolutionSource R C E F
local notation "A0" => dgModuleAugmentationSource R C E F
local notation "B0" => dgModuleAugmentationTarget R C E F
lemma dgModuleAugmentationRawFactorCoreIso_hom_naturality
    (H0 H1 : DGFunctor R (RightModule R E) (RightModule R K))
    (hq0 : ∀ X : T, moduleQuasiIso R K (H0.onClosed.map X.augmentation))
    (hq1 : ∀ X : T, moduleQuasiIso R K (H1.onClosed.map X.augmentation))
    (d : FunctorHom (dgNerve.map H0 ≫ L) (dgNerve.map H1 ≫ L)) :
    (dgModuleAugmentationRawFactorCoreIso R C E K F H0 hq0).hom ≫
      functorHomPrecomp (dgNerve.map (F.comp H0) ≫ L)
        (dgNerve.map (F.comp H1) ≫ L) (dgNerve.map P0)
        (dgModuleRawOutputPrecompHom R E K C F H0 H1 d) =
    functorHomPrecomp (dgNerve.map ((I).comp H0) ≫ L)
        (dgNerve.map ((I).comp H1) ≫ L) (dgNerve.map G)
        (dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) I H0 H1 d) ≫
      (dgModuleAugmentationRawFactorCoreIso R C E K F H1 hq1).hom := by
  have hs (H : DGFunctor R (RightModule R E) (RightModule R K)) :
      dgNerve.map G ≫ dgNerve.map ((I).comp H) ≫ L =
        dgNerve.map A0 ≫ dgNerve.map H ≫ L := by
    simp only [dgModuleAugmentationSource, dgNerve.map_comp, Category.assoc]
  have ht (H : DGFunctor R (RightModule R E) (RightModule R K)) :
      dgNerve.map P0 ≫ dgNerve.map (F.comp H) ≫ L =
        dgNerve.map B0 ≫ dgNerve.map H ≫ L := by
    simp only [dgModuleAugmentationTarget, dgNerve.map_comp, Category.assoc]
  have hc0 := functorIso_hom_heq_of_endpoint_heq
    (dgModuleAugmentationRawFactorCoreIso R C E K F H0 hq0)
    (dgModuleAugmentationRawFactorIso R C E K F H0 hq0) (hs H0) (ht H0)
    (dgModuleAugmentationRawFactorCoreIso_heq R C E K F H0 hq0)
  have hc1 := functorIso_hom_heq_of_endpoint_heq
    (dgModuleAugmentationRawFactorCoreIso R C E K F H1 hq1)
    (dgModuleAugmentationRawFactorIso R C E K F H1 hq1) (hs H1) (ht H1)
    (dgModuleAugmentationRawFactorCoreIso_heq R C E K F H1 hq1)
  have hr := dgModuleRawOutputPrecompHom_precomp_heq R E K C T F P0 H0 H1 d
  have hq := dgModuleRawOutputPrecompHom_precomp_heq R E K
    (SemifreeDGModules R E) T I G H0 H1 d
  exact functorHom_two_two_eq_of_heq
    (f := dgNerve.map G ≫ dgNerve.map ((I).comp H0) ≫ L)
    (g := dgNerve.map P0 ≫ dgNerve.map (F.comp H0) ≫ L)
    (h := dgNerve.map G ≫ dgNerve.map ((I).comp H1) ≫ L)
    (k := dgNerve.map P0 ≫ dgNerve.map (F.comp H1) ≫ L)
    _ _ _ _ _ _ _ _ (hs H0) (ht H0) (hs H1) (ht H1) hc0 hr hq hc1
    (dgModuleAugmentationRawFactorIso_hom_naturality R C E K F H0 H1 hq0 hq1 d)
end SerrePositivity.InfinityCategories
