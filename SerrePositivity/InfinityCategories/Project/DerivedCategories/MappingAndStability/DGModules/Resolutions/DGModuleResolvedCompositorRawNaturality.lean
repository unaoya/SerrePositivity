module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleResolvedAugmentationHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.IsoRawFactorSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoPrecompNaturalitySquare
/-!
概要：同じ分解・augmentation・通常比較の raw 四角形から元の合成比較の自然性を得る。
方針：任意の dg 加群値関手について三段経路を接続し、指定 raw factor を相殺する。
規約：比較を選び直さず追加の平坦性を要求しない。使われ方：元の κ の右変数自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (A : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R A]
  (E K : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (H0 H1 : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.RightModule R K))
  (G0 G1 : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A (_root_.SerrePositivity.DifferentialGraded.RightModule R K))
local notation "I" => _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K
  (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R K))
local notation "U0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) K (DGFunctor.comp I H0)
local notation "U1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) K (DGFunctor.comp I H1)
local notation "V0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R A K G0
local notation "V1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R A K G1
local notation "J" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R A E F
local notation "r0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) K
  (_root_.SerrePositivity.DifferentialGraded.DGFunctor.comp I H0)
local notation "r1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) K
  (_root_.SerrePositivity.DifferentialGraded.DGFunctor.comp I H1)
local notation "t0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R A K G0
local notation "t1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R A K G1
lemma dgModuleResolved_compositor_hom_naturality_of_raw
    (hq0 : ∀ X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E F,
      _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H0.onClosed.map X.augmentation))
    (hq1 : ∀ X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E F,
      _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H1.onClosed.map X.augmentation))
    (c0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F.comp H0)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G0))
    (c1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F.comp H1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G1))
    (k0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (J ≫ U0) V0) (k1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (J ≫ U1) V1)
    (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H0 ≫ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H1 ≫ L))
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U0 U1) (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V0 V1)
    (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G0 ≫ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G1 ≫ L))
    (ha : (r0).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R E K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) I H0 H1 d =
      a ≫ (r1).hom)
    (ht : (t0).hom ≫ e = b ≫ (t1).hom)
    (hc : (c0.postcomp L).hom ≫ e =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R E K A F H0 H1 d ≫ (c1.postcomp L).hom)
    (hk0 : k0.hom ≫ (t0).hom = ((r0).precomp J).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso R A E K F H0 hq0).hom ≫
        (c0.postcomp L).hom)
    (hk1 : k1.hom ≫ (t1).hom = ((r1).precomp J).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso R A E K F H1 hq1).hom ≫
        (c1.postcomp L).hom) :
    k0.hom ≫ b = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp U0 U1 J a ≫ k1.hom := by
  have hA := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_iso_square_forward r0 r1 a
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R E K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) I H0 H1 d) J ha
  have hB := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso_hom_naturality
    R E K A F H0 H1 hq0 hq1 d
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.iso_compositor_square_of_three_step_raw k0 k1 t0 t1
    ((r0).precomp J) ((r1).precomp J)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso R A E K F H0 hq0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso R A E K F H1 hq1)
    (c0.postcomp L) (c1.postcomp L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp U0 U1 J a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGFunctor.comp I H0) ≫ L)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGFunctor.comp I H1) ≫ L) J
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R E K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) I H0 H1 d))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRawOutputPrecompHom R E K A F H0 H1 d) e b hk0 hk1 hA.symm hB hc ht
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
