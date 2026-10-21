module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatCompatibilityInclusion
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationHomotopy
/-!
概要：同じ kernel の出力分解 augmentation を実 K-flat 圏内の全単体ホモトピーで表す。
方針：元の円柱射と両端の厳密包含式を保ち、頂点全部分圏の標準持ち上げを使う。
規約：出力の射影性や原 Hom の平坦性を追加しない。使われ方：K-flat 合成子の共通経路。
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
/-- 同じ kernel の実出力分解 augmentation を、K-flat 全部分圏内の全円柱へ持ち上げる。 -/
def dgRelativeKFlatKernelResolutionAugmentationHomotopy :
    SSet.Homotopy
      (dgKernelDerivedInfinity R D E P ≫ dgSemifreeToRelativeKFlatNerve R E)
      (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP) := by
  let B := dgModuleResolvedAugmentationHomotopy R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E P)
  have h₀ : dgModuleResolvedInfinity R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P) ≫
      dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)) =
      (dgKernelDerivedInfinity R D E P ≫ dgSemifreeToRelativeKFlatNerve R E) ≫
        dgRelativeKFlatModuleInclusion R E := by
    simp only [Category.assoc, dgSemifreeToRelativeKFlatNerve_inclusion]
    rfl
  have h₁ : dgNerve.map (dgSemifreeKernelModuleDG R D E P) =
      (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP) ≫
        dgRelativeKFlatModuleInclusion R E := by
    rw [Category.assoc, dgRelativeKFlatKernelNerve_inclusion, ← Category.assoc,
      dgSemifreeToRelativeKFlatNerve_inclusion]
    exact dgNerve.map_comp _ _
  let B' : SSet.Homotopy
      ((dgKernelDerivedInfinity R D E P ≫ dgSemifreeToRelativeKFlatNerve R E) ≫
        dgRelativeKFlatModuleInclusion R E)
      ((dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelNerve R D E P hP) ≫
        dgRelativeKFlatModuleInclusion R E) :=
    { h := B.h
      h₀ := by simpa only [h₀] using! B.h₀
      h₁ := by simpa only [h₁] using! B.h₁
      rel := B.rel }
  exact fullSubcomplexHomotopyLift (dgModuleRelativeKFlatVertex R E) _ _ B'
/-- 持ち上げた kernel augmentation は、実包含後に元の同じ resolved 円柱を回収する。 -/
lemma dgRelativeKFlatKernelResolutionAugmentationHomotopy_ι :
    (dgRelativeKFlatKernelResolutionAugmentationHomotopy R D E P hP).h ≫
      dgRelativeKFlatModuleInclusion R E =
    (dgModuleResolvedAugmentationHomotopy R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P)).h := by
  unfold dgRelativeKFlatKernelResolutionAugmentationHomotopy
  exact fullSubcomplexHomotopyLift_ι _ _ _ _
end SerrePositivity.InfinityCategories
