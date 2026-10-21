module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositionPath
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatRestrictionHom
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionRawFactorHom
/-!
概要：K-flat 合成子計算の左右の経路を、元の raw factor の指定経路へ戻す。
方針：既存の各指定射の HEq と二段経路比較を合成する。
規約：元の比較と実 augmentation を保持する。使われ方：元の導来合成子の共通経路。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
  (P : Bimodule R E D) (Q : Bimodule R K E)
/-- 元の指定合成子の後の同じ制限比較を、元の raw factor 経路へ戻す。 -/
lemma dgRelativeKFlatKernelComposition_left_raw_hom_heq
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    HEq ((dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP).hom ≫
      (dgRelativeKFlatKernelRestrictionNerveIso R D K (BimoduleTensor.compose R K E D Q P)
        (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)).hom)
    ((dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E K P Q hP).hom ≫
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) K
        (dgSemifreeKernelModuleDG R D K (BimoduleTensor.compose R K E D Q P))).hom) := by
  exact functorHom_comp_heq _ _ _ _ rfl rfl
    (dgRelativeKFlatKernelNerve_semifree_resolution R D K (BimoduleTensor.compose R K E D Q P)
      (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP)) (HEq.refl _)
    (dgRelativeKFlatKernelRestrictionNerveIso_hom_heq R D K (BimoduleTensor.compose R K E D Q P)
      (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP))
/-- 同じ制限比較・実 augmentation・通常合成比較の三段経路を元の raw 経路へ戻す。 -/
lemma dgRelativeKFlatKernelComposition_right_raw_hom_heq
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    HEq (((dgRelativeKFlatKernelRestrictionNerveIso R E K Q hQ).precomp
      (dgKernelDerivedInfinity R D E P)).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP)
          (dgRelativeKFlatKernelNerve R E K Q hQ ≫ dgRelativeKFlatResolution R K))) ≫
      (((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
        (dgSemifreeToRelativeKFlatNerve R D)).postcomp (dgRelativeKFlatResolution R K)).hom)
    (((dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
      (dgSemifreeKernelModuleDG R E K Q)).precomp (dgKernelDerivedInfinity R D E P)).hom ≫
      (dgModuleResolvedAugmentationRawFactorIso R (SemifreeDGModules R D) E K
        (dgSemifreeKernelModuleDG R D E P) (Morita.kernelTensor R E K Q)
        (dgKernelResolutionAugmentation_tensor_quasiIso R D E K P Q hP)).hom ≫
      ((dgKernelTensorCompositionSemifreeIso R D E K P Q).postcomp
        (dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))).hom)
    := by
  have hu := functorHomotopy_endpoints_of_raw_eq _ _
    (dgRelativeKFlatKernelAugmentation_post_kernel_raw R D E P hP K Q hQ)
  exact functorHom_comp_heq _ _ _ _ rfl hu.1
    (dgRelativeKFlatKernelNerve_semifree_resolution R D K (BimoduleTensor.compose R K E D Q P)
      (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP))
    (dgRelativeKFlatKernelRestrictionNerveIso_precomp_hom_heq
      R E K Q hQ _ (dgKernelDerivedInfinity R D E P))
    (dgRelativeKFlatKernelAugmentation_composition_hom_heq R D E K P Q hP hQ)
end SerrePositivity.InfinityCategories
