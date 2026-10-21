module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelAugmentationPost
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawEndpoints
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompositionSemifree
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationRawFactorHom
/-!
概要：同じ K-flat augmentation と通常合成比較の射を、元の raw 比較の射へ戻す。
方針：実円柱の等式から端点を回収し、指定同型の射と照合する。
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
/-- 同じ通常後続 augmentation の類は、元の raw factor 比較の順方向射。 -/
lemma dgRelativeKFlatKernelAugmentation_post_kernel_hom_heq
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    HEq (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP)
        (dgRelativeKFlatKernelNerve R E K Q hQ ≫ dgRelativeKFlatResolution R K))))
      (dgModuleResolvedAugmentationRawFactorIso R (SemifreeDGModules R D) E K
        (dgSemifreeKernelModuleDG R D E P) (Morita.kernelTensor R E K Q)
        (dgKernelResolutionAugmentation_tensor_quasiIso R D E K P Q hP)).hom := by
  have h := functorHomotopyHom_heq_of_raw_eq _ _
    (dgRelativeKFlatKernelAugmentation_post_kernel_raw R D E P hP K Q hQ)
  exact h.trans (heq_of_eq (dgModuleResolvedAugmentationRawFactorIso_hom
    R (SemifreeDGModules R D) E K (dgSemifreeKernelModuleDG R D E P)
      (Morita.kernelTensor R E K Q)
      (dgKernelResolutionAugmentation_tensor_quasiIso R D E K P Q hP)).symm)
/-- 同じ K-flat 合成比較の半自由制限・分解後の射は、元の通常 tensor 比較の像。 -/
lemma dgRelativeKFlatKernelCompositionIso_semifree_resolution_hom_heq
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    HEq (((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).precomp
      (dgSemifreeToRelativeKFlatNerve R D)).postcomp (dgRelativeKFlatResolution R K)).hom
      ((dgKernelTensorCompositionSemifreeIso R D E K P Q).postcomp
        (dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))).hom := by
  have hu := functorHomotopy_endpoints_of_raw_eq _ _
    (dgRelativeKFlatKernelAugmentation_post_kernel_raw R D E P hP K Q hQ)
  exact functorIso_hom_heq _ _ hu.2
    (dgRelativeKFlatKernelNerve_semifree_resolution R D K (BimoduleTensor.compose R K E D Q P)
      (Bimodule.rightRelativeKFlat_compose R K E D Q P hQ hP))
    (dgRelativeKFlatKernelCompositionIso_semifree_resolution_heq R D E K P Q hP hQ)
end SerrePositivity.InfinityCategories
