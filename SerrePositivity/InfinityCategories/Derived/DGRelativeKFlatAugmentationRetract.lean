module
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.Derived.DGResolutionAugmentationRetract
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Derived.FunctorHomFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawEndpoints
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorIsoWhiskerHEq
public import SerrePositivity.InfinityCategories.Core.CatInfinity.FunctorEqIsoTransport
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 半自由模型から同じ K-flat 全部分圏への包含は充満忠実。 -/
lemma dgSemifreeToRelativeKFlatNerve_isFullyFaithful :
    IsFullyFaithful (dgSemifreeToRelativeKFlatNerve R D) := by
  apply (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R D)
    (dgModuleRelativeKFlatVertex R D)).cancel_right
  change IsFullyFaithful
    (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatModuleInclusion R D)
  rw [dgSemifreeToRelativeKFlatNerve_inclusion]
  exact dgSemifreeModulesInclusion_isFullyFaithful R D
/-- 同じ augmentation からの戻り同型を、K-flat 分解の端点へ揃える。 -/
def dgRelativeKFlatAugmentationRetractIso :
    FunctorIso (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatResolution R D)
      (𝟙 (dgModuleDerivedInfinityCategory R D)) := by
  refine F2.functorIsoOfEq (dgModuleResolutionAugmentationRetractIso R D) ?_ rfl
  rw [dgRelativeKFlatResolution, ← Category.assoc, dgSemifreeToRelativeKFlatNerve_inclusion]
/-- K-flat の端点へ揃えても元の augmentation の戻り同型の値を保持する。 -/
lemma dgRelativeKFlatAugmentationRetractIso_heq :
    HEq (dgRelativeKFlatAugmentationRetractIso R D)
      (dgModuleResolutionAugmentationRetractIso R D) := by
  unfold dgRelativeKFlatAugmentationRetractIso
  exact F2.functorIsoOfEq_heq _ _ _
/-- 同じ戻り同型の半自由包含後の射は、元の K-flat 変形円柱の制限の類。 -/
lemma dgRelativeKFlatAugmentationRetractIso_postcomp_hom :
    ((dgRelativeKFlatAugmentationRetractIso R D).postcomp
      (dgSemifreeToRelativeKFlatNerve R D)).hom =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPrecomp (dgRelativeKFlatResolutionAugmentationHomotopy R D)
        (dgSemifreeToRelativeKFlatNerve R D))) := by
  let j := dgSemifreeToRelativeKFlatNerve R D
  let k := dgRelativeKFlatModuleInclusion R D
  let a := dgRelativeKFlatAugmentationRetractIso R D
  let b := dgModuleResolutionAugmentationRetractIso R D
  let i := dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
    (dgModuleSemifreeProperty R D))
  let A := functorHomotopyPostcomp
    (functorHomotopyPrecomp (dgRelativeKFlatResolutionAugmentationHomotopy R D) j) k
  let B := dgModuleResolutionSemifreeAugmentationHomotopy R D
  have hh : A.h = B.h := by
    change (j ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (dgRelativeKFlatResolutionAugmentationHomotopy R D).h ≫ k = _
    change (j ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (dgRelativeKFlatResolutionAugmentationHomotopy R D).h ≫
        dgRelativeKFlatModuleInclusion R D = _
    rw [dgRelativeKFlatResolutionAugmentationHomotopy_ι]
    change (j ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (k ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
        (dgModuleResolutionAugmentationHomotopy R D).h = _
    rw [← Category.assoc, ← comp_whiskerRight]
    change ((dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatModuleInclusion R D) ▷
      (Δ[1] : SSet.{max (u + 1) v})) ≫ _ = _
    rw [dgSemifreeToRelativeKFlatNerve_inclusion]
    rfl
  have ha := functorHomotopy_endpoints_of_raw_eq A B hh
  have hs : i ≫ dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id (RightModule R D)) =
      j ≫ dgRelativeKFlatResolution R D := by
    rw [dgRelativeKFlatResolution, ← Category.assoc, dgSemifreeToRelativeKFlatNerve_inclusion]
  have h0 := F2.functorIso_postcomp_postcomp_heq_of_heq b a hs rfl
    (dgRelativeKFlatAugmentationRetractIso_heq R D) j k
  have h1 := heq_of_eq (F2.functorIso_postcomp_postcomp b j k)
  have h2 := F2.functorIso_postcomp_heq_of_map_eq b (dgSemifreeToRelativeKFlatNerve_inclusion R D)
  have hi := h0.trans (h1.trans h2)
  have hiHom := functorIso_hom_heq ((a.postcomp j).postcomp k) (b.postcomp i) ha.1 ha.2 hi
  have he : ((a.postcomp j).postcomp k).hom =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy A) :=
    eq_of_heq (hiHom.trans ((heq_of_eq (dgModuleResolutionAugmentationRetractIso_postcomp_hom
      R D)).trans (functorHomotopyHom_heq_of_raw_eq A B hh).symm))
  apply functorHom_postcomp_injective_of_isFullyFaithful
    (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R D)
      (dgModuleRelativeKFlatVertex R D))
  simpa only [F2.functorIso_postcomp_hom, functorHomotopyPostcomp_hom] using! he
end SerrePositivity.InfinityCategories
