module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleDiskCoverStrictLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKernelCellStrictLift
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
/-!
概要：canonical 分解の全 cell 段に整合する strict lift を再帰する。
方針：初期 disk 被覆と後続 kernel cell の実持ち上げ・余極限の普遍性を使う。
規約：augmentation と各段への制限は厳密。使われ方：双加群模型の strict lift。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) {T N : ModuleCategory R D} (g : M ⟶ N) (q : T ⟶ N)
  (hqs : moduleDegreewiseSurjective R D q) (hqq : moduleQuasiIso R D q)
def dgModuleResolutionStrictLiftStages : (n : ℕ) →
    { b : (moduleResolutionStage R D M n).left ⟶ T //
        b ≫ q = (moduleResolutionStage R D M n).hom ≫ g }
  | 0 => ⟨Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDiskCover_strict_lift R D M q hqs
      (moduleDiskCoverπ R D M ≫ g)),
      Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDiskCover_strict_lift R D M q hqs
        (moduleDiskCoverπ R D M ≫ g))⟩
  | n + 1 => ⟨Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKernelCellStep_strict_lift R D
      (moduleResolutionStage R D M n).hom g q hqs hqq
      (dgModuleResolutionStrictLiftStages n).val
      (dgModuleResolutionStrictLiftStages n).property),
      (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKernelCellStep_strict_lift R D
        (moduleResolutionStage R D M n).hom g q hqs hqq
        (dgModuleResolutionStrictLiftStages n).val
        (dgModuleResolutionStrictLiftStages n).property)).2⟩
lemma dgModuleResolutionStrictLiftStages_succ (n : ℕ) :
    (moduleResolutionTransition R D M n).left ≫
        (dgModuleResolutionStrictLiftStages R D M g q hqs hqq (n + 1)).val =
      (dgModuleResolutionStrictLiftStages R D M g q hqs hqq n).val := by
  exact (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKernelCellStep_strict_lift R D
    (moduleResolutionStage R D M n).hom g q hqs hqq
    (dgModuleResolutionStrictLiftStages R D M g q hqs hqq n).val
    (dgModuleResolutionStrictLiftStages R D M g q hqs hqq n).property)).1
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
