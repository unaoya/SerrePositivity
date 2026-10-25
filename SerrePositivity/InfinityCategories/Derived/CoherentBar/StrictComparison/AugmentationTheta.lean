module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationEdge
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomExchange

/-!
概要：strict augmentation は bar の theta を消す。
方針：零次元・一次元・高次元の全列で判定し、正規化射影を介して移す。
規約：同じ正規化 theta と元の余錐を使う。
使われ方：実正規化 dg 加群からの標準 augmentation の閉性。
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

set_option maxHeartbeats 800000 in
-- The dimension split compares selected Hom ends with dependent simplex labels.
lemma dgCoherentBarStrictAugmentation_postColumn
    (s : dgCoherentBarIndex (nerve J)) :
    (eHomWhiskerLeft (Complex R)
      (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) s)
      (dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
        (dgCoherentBarColumn R D (dgCoherentBarStrictDiagram R D F) s) = 0 := by
  rcases s with ⟨n, s⟩
  cases n with
  | zero => rw [dgCoherentBarColumn, map_zero]
  | succ n =>
    cases n with
    | zero =>
      rw [dgCoherentBarStrictColumn R D F s]
      erw [Fin.sum_univ_one]
      have h1 : ((0 : ℤ) + 1 + ((0 : Fin 1).val : ℤ) + 1).negOnePow = (1 : ℤˣ) := rfl
      have h0 : ((0 : ℤ) + 1).negOnePow = (-1 : ℤˣ) := rfl
      erw [h1, h0]
      erw [one_smul, map_add]
      simp only [Units.smul_def, map_zsmul]
      have he := (dgCoherentBarStrictAugmentation_postFace_edge R D F c s).trans
        (dgCoherentBarStrictAugmentation_postPrefix_edge R D F c s).symm
      simpa only [Units.val_neg, Units.val_one, neg_one_zsmul, sub_eq_add_neg] using!
        (sub_eq_zero.mpr he)
    | succ n => convert! dgCoherentBarStrictAugmentation_postColumn_high R D F c s using 1

lemma dgCoherentBarStrictAugmentation_postTheta :
    (eHomWhiskerLeft (Complex R)
      (dgCoherentBarGraded R D (dgCoherentBarStrictDiagram R D F))
      (dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
        (dgCoherentBarTheta R D (dgCoherentBarStrictDiagram R D F)) = 0 := by
  apply (dgCoherentBarHomEquiv R D (dgCoherentBarStrictDiagram R D F) c.pt 1).injective
  rw [map_zero]
  funext s
  rw [dgCoherentBarHomEquiv_apply]
  have h := congrArg (fun f => f.f 1
    (dgCoherentBarTheta R D (dgCoherentBarStrictDiagram R D F)))
    (eHom_whisker_exchange (Complex R)
      (Sigma.ι (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)) s)
      (dgCoherentBarStrictAugmentationRawGraded R D F c))
  change (eHomWhiskerRight (Complex R)
      (Sigma.ι (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)) s) c.pt).f 1
      ((eHomWhiskerLeft (Complex R)
        (dgCoherentBarGraded R D (dgCoherentBarStrictDiagram R D F))
        (dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
          (dgCoherentBarTheta R D (dgCoherentBarStrictDiagram R D F))) =
    (eHomWhiskerLeft (Complex R)
      (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) s)
      (dgCoherentBarStrictAugmentationRawGraded R D F c)).f 1
      ((eHomWhiskerRight (Complex R)
        (Sigma.ι (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)) s)
        (dgCoherentBarGraded R D (dgCoherentBarStrictDiagram R D F))).f 1
          (dgCoherentBarTheta R D (dgCoherentBarStrictDiagram R D F))) at h
  rw [h, dgCoherentBarTheta_restrict, dgCoherentBarStrictAugmentation_postColumn R D F c]
  rfl

lemma dgCoherentBarStrictAugmentation_postNormalizedTheta :
    (eHomWhiskerLeft (Complex R)
      (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))
      (dgCoherentBarStrictAugmentationGraded R D F c)).f 1
        (dgCoherentBarNormalizedTheta R D (dgCoherentBarStrictDiagram R D F)) = 0 := by
  unfold dgCoherentBarNormalizedTheta
  rw [← dgStrictHom_whisker_exchange R D,
    ← dgStrictPostcompose_comp R D,
    dgCoherentBarStrictAugmentation_projection R D F c,
    dgCoherentBarStrictAugmentation_postTheta R D F c, map_zero]

end SerrePositivity.InfinityCategories
