module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedComparisonRawSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleInputUpAugmentationSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationPrecompCylinders
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyRawEndpoints
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 元の指定 resolved 前合成比較と元の実 augmentation は、全関手射の正方形を満たす。 -/
lemma dgModuleResolvedInfinity_precompIso_augmentation_heq :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A C E H F).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)))).hom ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R C E F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H))))
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R A E (H.comp F)))) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)
  let S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F)
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
    (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
  let UA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A)
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F)
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompSourceIso R A C E H F
  let L := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R C E F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)
  let L' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationInputBaseHomotopy R C E F)
    (UA ≫ h ≫ S.inv)
  let T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R A E (H.comp F)
  let T' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationInputBaseHomotopy R C E F)
    (UA ≫ Q.inv ≫ J)
  have hL : L.h = L'.h :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy_precomp_inputBase_raw R A C E H F
  have hT : T.h = T'.h :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy_precomp_source_raw R A C E H F
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopy_endpoints_of_raw_eq L L' hL
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopy_endpoints_of_raw_eq T T' hT
  have hIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso_rawSource_heq R C E F A H
  have hHom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A C E H F).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E))))
    ((e.precomp UA).postcomp r) ht.1 hl.1 hIso
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_comp_heq _ _ _ _ ht.1 hl.1 hl.2 hHom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq L L' hL)
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompSourceIso_inputUp_augmentation_heq R A C E H F
  exact hp.trans (hs.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq T' T hT.symm))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
