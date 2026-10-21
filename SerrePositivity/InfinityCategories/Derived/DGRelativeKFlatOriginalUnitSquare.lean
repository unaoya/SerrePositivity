module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedUnitInclusion
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelUnit
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelAugmentation
public import SerrePositivity.InfinityCategories.Derived.FunctorHomFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawEndpoints
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyInputExchange
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransportAlgebra
/-!
概要：元の導来対角単位を、K-flat 圏内の同じ augmentation と通常単位の経路へ同定する。
方針：実包含後の元の単位の式を回収し、全関手射の充満忠実性で反映する。
規約：指定単位と実円柱を変更しない。使われ方：K-flat 単位の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の導来単位の半自由包含像は、同じ K-flat augmentation と通常対角単位の経路。 -/
lemma dgKernelDerivedInfinity_identityIso_kflat_augmentation :
    ((dgKernelDerivedInfinity_identityIso R D).postcomp
      (dgSemifreeToRelativeKFlatNerve R D)).hom =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D D (Bimodule.diagonal R D)
        (Bimodule.diagonal_rightRelativeKFlat R D))) ≫
      ((dgRelativeKFlatKernelIdentityIso R D).precomp
        (dgSemifreeToRelativeKFlatNerve R D)).hom := by
  let j := dgSemifreeToRelativeKFlatNerve R D
  let k := dgRelativeKFlatModuleInclusion R D
  let i := dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
    (dgModuleSemifreeProperty R D))
  let d := dgKernelDerivedInfinity_identityIso R D
  let u := dgRelativeKFlatKernelIdentityIso R D
  let w := dgKernelIdentityNerveIso R D
  let H := dgRelativeKFlatKernelResolutionAugmentationHomotopy R D D (Bimodule.diagonal R D)
    (Bimodule.diagonal_rightRelativeKFlat R D)
  let A := functorHomotopyPostcomp H k
  let B := dgModuleResolvedAugmentationHomotopy R (SemifreeDGModules R D) D
    (dgSemifreeKernelModuleDG R D D (Bimodule.diagonal R D))
  have hh : A.h = B.h := dgRelativeKFlatKernelResolutionAugmentationHomotopy_ι R D D
    (Bimodule.diagonal R D) (Bimodule.diagonal_rightRelativeKFlat R D)
  have ha := functorHomotopy_endpoints_of_raw_eq A B hh
  have ht : ((𝟙 (dgModuleDerivedInfinityCategory R D)) ≫ j) ≫ k =
      (𝟙 (dgModuleDerivedInfinityCategory R D)) ≫ i := by
    simp only [Category.id_comp]
    exact dgSemifreeToRelativeKFlatNerve_inclusion R D
  have hv := (heq_of_eq (F2.functorIso_postcomp_postcomp d j k)).trans
    (F2.functorIso_postcomp_heq_of_map_eq d (dgSemifreeToRelativeKFlatNerve_inclusion R D))
  have hvHom := functorIso_hom_heq ((d.postcomp j).postcomp k) (d.postcomp i) ha.1 ht hv
  have hs := dgRelativeKFlatKernelNerve_inclusion R D D (Bimodule.diagonal R D)
    (Bimodule.diagonal_rightRelativeKFlat R D)
  have hg : k ≫ (𝟙 (dgModuleNerve R D)) =
      (𝟙 (dgRelativeKFlatModuleNerve R D)) ≫ k := by
    rw [Category.comp_id, Category.id_comp]
  have hu0 := F2.functorIso_precomp_heq_of_heq (w.precomp k) (u.postcomp k) hs.symm hg
    (dgRelativeKFlatKernelIdentityIso_inclusion_heq R D) j
  have hu := (heq_of_eq (F2.functorIso_precomp_postcomp u j k)).trans
    (hu0.trans ((heq_of_eq (F2.functorIso_precomp_precomp w k j)).trans
      (F2.functorIso_precomp_heq_of_map_eq w (dgSemifreeToRelativeKFlatNerve_inclusion R D))))
  have huHom := functorIso_hom_heq ((u.precomp j).postcomp k) (w.precomp i) ha.2 ht hu
  have hright := functorHom_comp_heq
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy A))
    ((u.precomp j).postcomp k).hom
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy B)) (w.precomp i).hom
    ha.1 ha.2 ht (functorHomotopyHom_heq_of_raw_eq A B hh) huHom
  have he : ((d.postcomp j).postcomp k).hom =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy A) ≫
        ((u.precomp j).postcomp k).hom :=
    eq_of_heq (hvHom.trans
      ((heq_of_eq (dgKernelDerivedInfinity_identityIso_inclusion_hom R D)).trans hright.symm))
  apply functorHom_postcomp_injective_of_isFullyFaithful
    (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R D)
      (dgModuleRelativeKFlatVertex R D))
  simpa only [F2.functorIso_postcomp_hom, functorHomotopyPostcomp_hom,
    CategoryTheory.Functor.map_comp] using! he
end SerrePositivity.InfinityCategories
