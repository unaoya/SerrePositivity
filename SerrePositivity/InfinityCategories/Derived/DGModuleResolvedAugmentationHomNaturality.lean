module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationCoreHomNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPrecompRetractionSquare
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationRawFactor
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
lemma dgModuleResolvedAugmentationRawFactorIso_hom_naturality
    (H0 H1 : DGFunctor R (RightModule R E) (RightModule R K))
    (hq0 : ∀ X : T, moduleQuasiIso R K (H0.onClosed.map X.augmentation))
    (hq1 : ∀ X : T, moduleQuasiIso R K (H1.onClosed.map X.augmentation))
    (d : FunctorHom (dgNerve.map H0 ≫ L) (dgNerve.map H1 ≫ L)) :
    (dgModuleResolvedAugmentationRawFactorIso R C E K F H0 hq0).hom ≫
      dgModuleRawOutputPrecompHom R E K C F H0 H1 d =
    functorHomPrecomp (dgNerve.map ((I).comp H0) ≫ L)
        (dgNerve.map ((I).comp H1) ≫ L) (dgModuleResolvedInfinity R C E F)
        (dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) I H0 H1 d) ≫
      (dgModuleResolvedAugmentationRawFactorIso R C E K F H1 hq1).hom := by
  let S := (dgModuleResolvedSourceSectionEquivalence R C E F).hom
  have hs : dgModuleResolvedInfinity R C E F = S ≫ dgNerve.map G := by
    simpa only [S, dgModuleResolvedSourceSectionEquivalence, Category.assoc] using!
      dgModuleResolvedInfinity_eq_section_replacement R C E F
  exact functorIso_square_precomp_retract S (dgNerve.map P0) (dgNerve.map G)
    (dgModuleResolvedInfinity R C E F)
    (dgModuleResolvedSourceSection_comp_source R C E F) hs.symm
    (dgNerve.map ((I).comp H0) ≫ L) (dgNerve.map ((I).comp H1) ≫ L)
    (dgNerve.map (F.comp H0) ≫ L) (dgNerve.map (F.comp H1) ≫ L)
    (dgModuleAugmentationRawFactorCoreIso R C E K F H0 hq0)
    (dgModuleAugmentationRawFactorCoreIso R C E K F H1 hq1)
    (dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) I H0 H1 d)
    (dgModuleRawOutputPrecompHom R E K C F H0 H1 d)
    (dgModuleAugmentationRawFactorCoreIso_hom_naturality R E K C F H0 H1 hq0 hq1 d)
    (dgModuleResolvedAugmentationRawFactorIso R C E K F H0 hq0)
    (dgModuleResolvedAugmentationRawFactorIso R C E K F H1 hq1)
    (dgModuleResolvedAugmentationRawFactorIso_heq R C E K F H0 hq0)
    (dgModuleResolvedAugmentationRawFactorIso_heq R C E K F H1 hq1)
end SerrePositivity.InfinityCategories
