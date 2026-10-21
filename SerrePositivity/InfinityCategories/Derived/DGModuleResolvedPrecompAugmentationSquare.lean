module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedComparisonRawSource
public import SerrePositivity.InfinityCategories.Derived.DGModuleInputUpAugmentationSquare
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationPrecompCylinders
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawEndpoints
/-!
概要：元の指定 resolved 前合成比較と同じ実 augmentation の正方形を照合する。
方針：入力 Up で制限した正方形へ、同じ円柱とその両端から元の全関手射を移す。
規約：非可逆な augmentation の指定値を保つ。使われ方：raw factor と K-flat 合成子の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v))
  [DGCategory R A] [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 元の指定 resolved 前合成比較と元の実 augmentation は、全関手射の正方形を満たす。 -/
lemma dgModuleResolvedInfinity_precompIso_augmentation_heq :
    HEq (((dgModuleResolvedInfinity_precompIso R A C E H F).postcomp
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)))).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp (dgModuleResolvedAugmentationHomotopy R C E F) (dgNerve.map H))))
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgModuleResolvedAugmentationHomotopy R A E (H.comp F)))) := by
  let Q := dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)
  let S := dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let J := dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F)
  let h := dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
    (H.comp (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
  let UA := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A)
  let r := dgNerve.map (dgModuleAugmentationSource R C E F)
  let e := dgModuleResolutionPrecompSourceIso R A C E H F
  let L := functorHomotopyPrecomp (dgModuleResolvedAugmentationHomotopy R C E F) (dgNerve.map H)
  let L' := functorHomotopyPrecomp (dgModuleAugmentationInputBaseHomotopy R C E F)
    (UA ≫ h ≫ S.inv)
  let T := dgModuleResolvedAugmentationHomotopy R A E (H.comp F)
  let T' := functorHomotopyPrecomp (dgModuleAugmentationInputBaseHomotopy R C E F)
    (UA ≫ Q.inv ≫ J)
  have hL : L.h = L'.h :=
    dgModuleResolvedAugmentationHomotopy_precomp_inputBase_raw R A C E H F
  have hT : T.h = T'.h :=
    dgModuleResolvedAugmentationHomotopy_precomp_source_raw R A C E H F
  have hl := functorHomotopy_endpoints_of_raw_eq L L' hL
  have ht := functorHomotopy_endpoints_of_raw_eq T T' hT
  have hIso := dgModuleResolvedInfinity_precompIso_rawSource_heq R C E F A H
  have hHom := functorIso_hom_heq
    ((dgModuleResolvedInfinity_precompIso R A C E H F).postcomp
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E))))
    ((e.precomp UA).postcomp r) ht.1 hl.1 hIso
  have hp := functorHom_comp_heq _ _ _ _ ht.1 hl.1 hl.2 hHom
    (functorHomotopyHom_heq_of_raw_eq L L' hL)
  have hs := dgModuleResolutionPrecompSourceIso_inputUp_augmentation_heq R A C E H F
  exact hp.trans (hs.trans (functorHomotopyHom_heq_of_raw_eq T' T hT.symm))
end SerrePositivity.InfinityCategories
