module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatAugmentationPrecomp
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelAugmentation
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorAugmentationEq
public import SerrePositivity.InfinityCategories.Derived.FunctorHomFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoWhiskerHEq
/-!
概要：元の半自由 kernel 制限比較と同じ augmentation の正方形を K-flat 圏内で証明する。
方針：実包含後に元の raw factor 正方形を回収し、全関手圏の充満忠実性で反映する。
規約：頂点成分や可逆な射に限定しない。使われ方：元の kernel 合成子の K-flat 経路照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalCategory MonoidalClosed
open scoped Simplicial
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
/-- 元の kernel 制限比較と同じ実 K-flat augmentation は、全関手射の正方形を満たす。 -/
lemma dgRelativeKFlatKernelRestrictionNerveIso_augmentation :
    ((dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).postcomp
      (dgSemifreeToRelativeKFlatNerve R E)).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp (dgRelativeKFlatResolutionAugmentationHomotopy R E)
          (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP))) =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP)) := by
  let k := dgRelativeKFlatModuleInclusion R E
  let J := dgSemifreeToRelativeKFlatNerve R E
  let r := dgRelativeKFlatKernelRestrictionNerveIso R D E P hP
  let r₀ := dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E P)
  let I := dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
    (dgModuleSemifreeProperty R E))
  let A := functorHomotopyPostcomp
    (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP) k
  let B := dgModuleResolvedAugmentationHomotopy R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E P)
  let C := functorHomotopyPostcomp
    (functorHomotopyPrecomp (dgRelativeKFlatResolutionAugmentationHomotopy R E)
      (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP)) k
  let T := functorHomotopyPrecomp (dgModuleResolutionAugmentationHomotopy R E)
    (dgNerve.map (dgSemifreeKernelModuleDG R D E P))
  have hA : A.h = B.h := dgRelativeKFlatKernelResolutionAugmentationHomotopy_ι R D E P hP
  have hC : C.h = T.h := dgRelativeKFlatResolutionAugmentationHomotopy_precomp_kernel_raw R D E P hP
  have ha := functorHomotopy_endpoints_of_raw_eq A B hA
  have hc := functorHomotopy_endpoints_of_raw_eq C T hC
  have h₀ := F2.functorIso_postcomp_postcomp_heq_of_heq r₀ r rfl
    (dgRelativeKFlatKernelNerve_semifree_resolution R D E P hP).symm
    (dgRelativeKFlatKernelRestrictionNerveIso_heq R D E P hP) J k
  have h₁ := heq_of_eq (F2.functorIso_postcomp_postcomp r₀ J k)
  have h₂ := F2.functorIso_postcomp_heq_of_map_eq r₀
    (dgSemifreeToRelativeKFlatNerve_inclusion R E)
  have hIso := h₀.trans (h₁.trans h₂)
  have hHom := functorIso_hom_heq ((r.postcomp J).postcomp k) (r₀.postcomp I)
    ha.1 hc.1 hIso
  have hLeft := functorHom_comp_heq ((r.postcomp J).postcomp k).hom
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy C))
    (r₀.postcomp I).hom
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy T))
    ha.1 hc.1 ha.2 hHom (functorHomotopyHom_heq_of_raw_eq C T hC)
  have hRaw := dgModuleResolvedInfinity_rawFactorIso_augmentation R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E P)
  have hRight := functorHomotopyHom_heq_of_raw_eq A B hA
  have hEq : ((r.postcomp J).postcomp k).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy C) =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy A) :=
    eq_of_heq (hLeft.trans ((heq_of_eq hRaw).trans hRight.symm))
  have hk : IsFullyFaithful k :=
    isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R E) (dgModuleRelativeKFlatVertex R E)
  exact functorIso_homotopy_square_of_postcomp k hk (r.postcomp J)
    (functorHomotopyPrecomp (dgRelativeKFlatResolutionAugmentationHomotopy R E)
      (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP))
    (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP) hEq
end SerrePositivity.InfinityCategories
