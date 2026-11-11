module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGResolutionAugmentationRetract
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyRawEndpoints
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerHEq
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
/-!
概要：同じ augmentation の戻り同型を K-flat の分解と元の変形円柱へ接続する。
方針：同じ指定値と円柱の前後合成を全関手射の等式で照合する。
規約：既存の導来単位を変更しない。使われ方：K-flat 単位の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 半自由模型から同じ K-flat 全部分圏への包含は充満忠実。 -/
lemma dgSemifreeToRelativeKFlatNerve_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R D)).cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModulesInclusion_isFullyFaithful R D
/-- 同じ augmentation からの戻り同型を、K-flat 分解の端点へ揃える。 -/
def dgRelativeKFlatAugmentationRetractIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) := by
  refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionAugmentationRetractIso R D) ?_ rfl
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve_inclusion]
/-- K-flat の端点へ揃えても元の augmentation の戻り同型の値を保持する。 -/
lemma dgRelativeKFlatAugmentationRetractIso_heq :
    HEq (dgRelativeKFlatAugmentationRetractIso R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionAugmentationRetractIso R D) := by
  unfold dgRelativeKFlatAugmentationRetractIso
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _
/-- 同じ戻り同型の半自由包含後の射は、元の K-flat 変形円柱の制限の類。 -/
lemma dgRelativeKFlatAugmentationRetractIso_postcomp_hom :
    ((dgRelativeKFlatAugmentationRetractIso R D).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D)).hom =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D))) := by
  let j := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D
  let k := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D
  let a := dgRelativeKFlatAugmentationRetractIso R D
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionAugmentationRetractIso R D
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D))
  let A := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy R D) j) k
  let B := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionSemifreeAugmentationHomotopy R D
  have hh : A.h = B.h := by
    change (j ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy R D).h ≫ k = _
    change (j ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy R D).h ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy_ι]
    change (j ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (k ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionAugmentationHomotopy R D).h = _
    rw [← Category.assoc, ← comp_whiskerRight]
    change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D) ▷
      (Δ[1] : SSet.{max (u + 1) v})) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve_inclusion]
    rfl
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopy_endpoints_of_raw_eq A B hh
  have hs : i ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id (RightModule R D)) =
      j ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve_inclusion]
  have h0 := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_postcomp_postcomp_heq_of_heq b a hs rfl
    (dgRelativeKFlatAugmentationRetractIso_heq R D) j k
  have h1 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp b j k)
  have h2 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_map_eq b (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve_inclusion R D)
  have hi := h0.trans (h1.trans h2)
  have hiHom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq ((a.postcomp j).postcomp k) (b.postcomp i) ha.1 ha.2 hi
  have he : ((a.postcomp j).postcomp k).hom =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy A) :=
    eq_of_heq (hiHom.trans ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionAugmentationRetractIso_postcomp_hom
      R D)).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq A B hh).symm))
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_injective_of_isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R D))
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom] using! he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
