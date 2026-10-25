module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Columns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationGraded
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColumns

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category J] (F : J ⥤ ModuleCategory R D) (c : Cocone F)

lemma dgCoherentBarStrictAugmentation_postInclusion {M : ModuleCategory R D}
    (s : dgCoherentBarIndex (nerve J)) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) s))).X q) :
    (eHomWhiskerLeft (Complex R) M (dgCoherentBarStrictAugmentationRawGraded R D F c)).f q
      ((eHomWhiskerLeft (Complex R) M
        (Sigma.ι (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)) s)).f q z) =
      (eHomWhiskerLeft (Complex R) M (dgCoherentBarStrictAugmentationRawColumn R D F c s)).f q z := by
  have h := congrArg (fun f => f.f q z)
    (eHomWhiskerLeft_comp (Complex R) M
      (Sigma.ι (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)) s)
      (dgCoherentBarStrictAugmentationRawGraded R D F c))
  change (eHomWhiskerLeft (Complex R) M
      (Sigma.ι (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)) s ≫
        dgCoherentBarStrictAugmentationRawGraded R D F c)).f q z = _ at h
  rw [dgCoherentBarStrictAugmentationRawGraded_ι R D F c s] at h
  exact h.symm

lemma dgCoherentBarStrictAugmentation_postPositiveInclusion {M : ModuleCategory R D}
    (s : dgCoherentBarIndex (nerve J)) (hs : 0 < s.1) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) s))).X q) :
    (eHomWhiskerLeft (Complex R) M (dgCoherentBarStrictAugmentationRawGraded R D F c)).f q
      ((eHomWhiskerLeft (Complex R) M
        (Sigma.ι (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)) s)).f q z) = 0 := by
  rw [dgCoherentBarStrictAugmentation_postInclusion R D F c s q z]
  rcases s with ⟨n, s⟩
  cases n with
  | zero => change 0 < 0 at hs; omega
  | succ n => exact dgCoherentBarHom_postcompose_zero R D q z

-- Face and prefix columns use distinct presentations of the same selected Hom end.
set_option maxHeartbeats 800000 in
lemma dgCoherentBarStrictAugmentation_postColumn_high {n : ℕ}
    (s : (nerve J) _⦋n + 2⦌) :
    (eHomWhiskerLeft (Complex R)
      (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨n + 2, s⟩)
      (dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
        (dgCoherentBarColumn R D (dgCoherentBarStrictDiagram R D F) ⟨n + 2, s⟩) = 0 := by
  rw [dgCoherentBarStrictColumn R D F s]
  simp only [map_add, map_sum, Units.smul_def, map_zsmul]
  have hf (i : Fin (n + 2)) :
      (eHomWhiskerLeft (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨n + 2, s⟩)
        (dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
          (dgCoherentBarFaceColumn R D (dgCoherentBarStrictDiagram R D F) s i) = 0 := by
    unfold dgCoherentBarFaceColumn
    rw [dgCoherentBarStrictAugmentation_postInclusion R D F c]
    exact dgCoherentBarHom_postcompose_zero R D 1 _
  have hp : (eHomWhiskerLeft (Complex R)
      (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨n + 2, s⟩)
      (dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
        (dgCoherentBarPrefixColumn R D (dgCoherentBarStrictDiagram R D F) s 0 (by omega)) = 0 := by
    unfold dgCoherentBarPrefixColumn
    rw [dgCoherentBarStrictAugmentation_postInclusion R D F c]
    exact dgCoherentBarHom_postcompose_zero R D 1 _
  simp only [hf, hp, smul_zero, Finset.sum_const_zero, zero_add]

end SerrePositivity.InfinityCategories
