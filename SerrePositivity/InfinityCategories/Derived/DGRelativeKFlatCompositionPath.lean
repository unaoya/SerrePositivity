module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyInputExchange
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositionHom
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelAugmentationPost
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawEndpoints
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositionSemifree
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationRawFactorHom
/-!
概要：K-flat augmentation と通常合成比較の二段経路を元の raw 経路へ戻す。
方針：実円柱から回収した端点等式と指定された二つの射の HEq を用いる。
規約：元の cochain と比較の値を保つ。使われ方：指定導来合成子の共通経路計算。
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
/-- 元の同じ augmentation と通常合成比較からなる二段経路は raw factor 経路と一致する。 -/
lemma dgRelativeKFlatKernelAugmentation_composition_hom_heq
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    HEq (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP)
          (dgRelativeKFlatKernelNerve R E K Q hQ ≫ dgRelativeKFlatResolution R K))) ≫
      (((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
        (dgSemifreeToRelativeKFlatNerve R D)).postcomp (dgRelativeKFlatResolution R K)).hom)
    ((dgModuleResolvedAugmentationRawFactorIso R (SemifreeDGModules R D) E K
        (dgSemifreeKernelModuleDG R D E P) (Morita.kernelTensor R E K Q)
        (dgKernelResolutionAugmentation_tensor_quasiIso R D E K P Q hP)).hom ≫
      ((dgKernelTensorCompositionSemifreeIso R D E K P Q).postcomp
        (dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))).hom)
    := by
  have hu := functorHomotopy_endpoints_of_raw_eq _ _
    (dgRelativeKFlatKernelAugmentation_post_kernel_raw R D E P hP K Q hQ)
  exact functorHom_comp_heq _ _ _ _ hu.1 hu.2
    (dgRelativeKFlatKernelNerve_semifree_resolution R D K (BimoduleTensor.compose R K E D Q P)
      (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP))
    (dgRelativeKFlatKernelAugmentation_post_kernel_hom_heq R D E K P Q hP hQ)
    (dgRelativeKFlatKernelCompositionIso_semifree_resolution_hom_heq R D E K P Q hP hQ)
end SerrePositivity.InfinityCategories
