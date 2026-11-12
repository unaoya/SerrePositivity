module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Columns
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AugmentationGraded
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColumns

/-!
概要：strict augmentation の後合成により、正次元標的の bar 係数は零になる。
方針：余積包含を通る係数の後合成を、対応する augmentation の列へ移す。
規約：NativeColumns から使うのは後合成零の代数的補題だけで、native 普遍性は使わない。
使われ方：標準 augmentation の bar 微分に関する閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (c : Cocone F)

lemma dgCoherentBarStrictAugmentation_postInclusion {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex (nerve J)) (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s))).X q) :
    (eHomWhiskerLeft (Complex R) M (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawGraded R D F c)).f q
      ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)) s)).f q z) =
      (eHomWhiskerLeft (Complex R) M (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawColumn R D F c s)).f q z := by
  have h := congrArg (fun f => f.f q z)
    (eHomWhiskerLeft_comp (_root_.SerrePositivity.DifferentialGraded.Complex R) M
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)) s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawGraded R D F c))
  change (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)) s ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawGraded R D F c)).f q z = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawGraded_ι R D F c s] at h
  exact h.symm

lemma dgCoherentBarStrictAugmentation_postPositiveInclusion {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex (nerve J)) (hs : 0 < s.1) (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s))).X q) :
    (eHomWhiskerLeft (Complex R) M (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawGraded R D F c)).f q
      ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)) s)).f q z) = 0 := by
  rw [dgCoherentBarStrictAugmentation_postInclusion R D F c s q z]
  rcases s with ⟨n, s⟩
  cases n with
  | zero => change 0 < 0 at hs; omega
  | succ n => exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_postcompose_zero R D q z

-- Face and prefix columns use distinct presentations of the same selected Hom end.
set_option maxHeartbeats 800000 in
lemma dgCoherentBarStrictAugmentation_postColumn_high {n : ℕ}
    (s : (nerve J) _⦋n + 2⦌) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨n + 2, s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨n + 2, s⟩) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColumn R D F s]
  simp only [map_add, map_sum, Units.smul_def, map_zsmul]
  have hf (i : Fin (n + 2)) :
      (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨n + 2, s⟩)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s i) = 0 := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn
    rw [dgCoherentBarStrictAugmentation_postInclusion R D F c]
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_postcompose_zero R D 1 _
  have hp : (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨n + 2, s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s 0 (by omega)) = 0 := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn
    rw [dgCoherentBarStrictAugmentation_postInclusion R D F c]
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_postcompose_zero R D 1 _
  simp only [hf, hp, smul_zero, Finset.sum_const_zero, zero_add]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
