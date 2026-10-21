module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelAugmentation
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationRawHomotopy
/-!
概要：K-flat 圏内の同じ kernel augmentation と、元の合成子の通常後続円柱を比較する。
方針：通常作用の実包含式と元の全円柱の射影式を使う。
規約：同じ全時刻の写像を保持する。使われ方：元の指定導来合成子の K-flat 経路計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
variable (K : Type v) [DGCategory R K] [Small.{u} K]
  (Q : Bimodule R K E) (hQ : Bimodule.rightRelativeKFlat R K E Q)
/-- 通常 K-flat kernel と分解を続けた同じ円柱は、元の合成子の通常後続円柱に等しい。 -/
lemma dgRelativeKFlatKernelAugmentation_post_kernel_raw :
    (functorHomotopyPostcomp (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP)
      (dgRelativeKFlatKernelNerve R E K Q hQ ≫ dgRelativeKFlatResolution R K)).h =
    (dgModuleResolvedAugmentationRawHomotopy R (SemifreeDGModules R D) E K
      (dgSemifreeKernelModuleDG R D E P) (Morita.kernelTensor R E K Q)).h := by
  change (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP).h ≫
    (dgRelativeKFlatKernelNerve R E K Q hQ ≫ dgRelativeKFlatResolution R K) =
      (dgModuleResolvedAugmentationHomotopy R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P)).h ≫ dgNerve.map (Morita.kernelTensor R E K Q) ≫
        dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))
  rw [dgRelativeKFlatKernelNerve_resolution]
  change (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP).h ≫
    dgRelativeKFlatModuleInclusion R E ≫ dgNerve.map (Morita.kernelTensor R E K Q) ≫
      dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)) = _
  rw [← Category.assoc (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP).h
    (dgRelativeKFlatModuleInclusion R E),
    dgRelativeKFlatKernelResolutionAugmentationHomotopy_ι]
end SerrePositivity.InfinityCategories
