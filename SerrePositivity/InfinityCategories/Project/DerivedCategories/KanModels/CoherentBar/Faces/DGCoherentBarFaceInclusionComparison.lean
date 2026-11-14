module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleUnitShiftBlockInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleClosedPostHEq
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarShiftedInclusions
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
概要：元の面列をシフト包含に合成した係数を、同じ削除単体の bar 包含へ戻す。
方針：閉余積包含との結合則、移送した単位ブロックの消去、符号の二乗一を使う。
規約：元の面ラベル・源と標的・全次数を保持する。
使われ方：実 bar の θ 作用と HA 右辺の削除項の一項ごとの比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarFaceColumn_comp_shiftIn_heq {n : ℕ} (σ : I _⦋n + 1⦌)
    (i : Fin (n + 1)) :
    HEq (compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F σ i)
      (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩))
      (show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega))
      ((n : ℤ).negOnePow • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace σ i.succ)) := by
  let M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩
  let N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace σ i.succ)
  have hMN : M = N := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D F σ i).symm
  have hb := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleUnitShiftBlock_comp_shiftIn_heq R D M N hMN
    ((n + 1 : ℕ) : ℤ) (n : ℤ) 1 (by omega) (by omega)
  change HEq (_root_.SerrePositivity.DifferentialGraded.compose R (x := M)
    (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
    (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace σ i.succ)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F σ i) (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) M)
    (show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega))
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D (n : ℤ) N) at hb
  let j := Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace σ i.succ)
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomClosedPost_heq R D
    (M := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
    (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace σ i.succ))
    (P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
    (M' := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
    (N' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace σ i.succ))
    (P' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) (k := -(n : ℤ)) (l := -(n : ℤ))
    (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)) hMN) rfl rfl rfl j j (HEq.refl _)
    _ _ hb
  have he := _root_.SerrePositivity.DifferentialGraded.moduleHomPostcomposition_compose R D
    (S := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
    (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, σ⟩)
    (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace σ i.succ))
    (P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) j
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F σ i) (show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega)
  have hs : (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N) j).f (-(n : ℤ))
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D (n : ℤ) N) =
      (n : ℤ).negOnePow • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace σ i.succ) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace, smul_smul, Int.units_mul_self, one_smul]
    rfl
  exact (heq_of_eq he).trans (hp.trans (heq_of_eq hs))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
