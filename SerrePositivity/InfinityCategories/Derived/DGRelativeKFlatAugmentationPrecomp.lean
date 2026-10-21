module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelRestrictionNerve
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompatibilityInclusion
/-!
概要：通常 kernel の半自由制限上で、K-flat 変形円柱の実包含後を計算する。
方針：同じ全円柱の射影式と通常作用の厳密包含式を使う。
規約：全時刻の実写像を保持する。使われ方：元の kernel augmentation の K-flat 正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
/-- 通常 kernel の半自由制限上の K-flat 変形円柱は、実包含後に同じ局所化円柱へ戻る。 -/
lemma dgRelativeKFlatResolutionAugmentationHomotopy_precomp_kernel_raw :
    (functorHomotopyPostcomp
      (functorHomotopyPrecomp (dgRelativeKFlatResolutionAugmentationHomotopy R E)
        (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP))
      (dgRelativeKFlatModuleInclusion R E)).h =
    (functorHomotopyPrecomp (dgModuleResolutionAugmentationHomotopy R E)
      (dgNerve.map (dgSemifreeKernelModuleDG R D E P))).h := by
  change ((dgSemifreeToRelativeKFlatNerve R D ≫
      dgRelativeKFlatKernelNerve R D E P hP) ▷ (Δ[1] : SSet)) ≫
      (dgRelativeKFlatResolutionAugmentationHomotopy R E).h ≫
        dgRelativeKFlatModuleInclusion R E = _
  rw [dgRelativeKFlatResolutionAugmentationHomotopy_ι]
  change ((dgSemifreeToRelativeKFlatNerve R D ≫
      dgRelativeKFlatKernelNerve R D E P hP) ▷ (Δ[1] : SSet)) ≫
      ((dgRelativeKFlatModuleInclusion R E ▷ (Δ[1] : SSet)) ≫
        (dgModuleResolutionAugmentationHomotopy R E).h) = _
  rw [← Category.assoc, ← comp_whiskerRight,
    dgRelativeKFlatKernelNerve_semifree_inclusion]
  rfl
end SerrePositivity.InfinityCategories
