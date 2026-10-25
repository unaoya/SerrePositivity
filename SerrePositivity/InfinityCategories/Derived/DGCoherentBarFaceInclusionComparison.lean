module
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnitShiftBlockInclusion
public import SerrePositivity.InfinityCategories.Derived.DGModuleClosedPostHEq
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarShiftedInclusions
public import SerrePositivity.DifferentialGraded.Module.HomPostcompositionComposition

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarFaceColumn_comp_shiftIn_heq {n : ℕ} (σ : I _⦋n + 1⦌)
    (i : Fin (n + 1)) :
    HEq (compose R (x := dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarFaceColumn R D F σ i)
      (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (dgCoherentBarSource R D F ⟨n + 1, σ⟩))
      (show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega))
      ((n : ℤ).negOnePow • dgCoherentBarShiftedInclusion R D F (dgCoherentBarFace σ i.succ)) := by
  let M := dgCoherentBarSource R D F ⟨n + 1, σ⟩
  let N := dgCoherentBarSource R D F (dgCoherentBarFace σ i.succ)
  have hMN : M = N := (dgCoherentBarSource_face_succ R D F σ i).symm
  have hb := dgModuleUnitShiftBlock_comp_shiftIn_heq R D M N hMN
    ((n + 1 : ℕ) : ℤ) (n : ℤ) 1 (by omega) (by omega)
  change HEq (compose R (x := M)
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F (dgCoherentBarFace σ i.succ)))
    (dgCoherentBarFaceBlock R D F σ i) (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) M)
    (show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega))
    (moduleShiftInElement R D (n : ℤ) N) at hb
  let j := Sigma.ι (dgCoherentBarFamily R D F) (dgCoherentBarFace σ i.succ)
  have hp := dgModuleHomClosedPost_heq R D
    (M := ForgetEnrichment.of (Complex R) M)
    (N := dgCoherentBarFamily R D F (dgCoherentBarFace σ i.succ))
    (P := dgCoherentBarGraded R D F)
    (M' := ForgetEnrichment.of (Complex R) N)
    (N' := dgCoherentBarFamily R D F (dgCoherentBarFace σ i.succ))
    (P' := dgCoherentBarGraded R D F) (k := -(n : ℤ)) (l := -(n : ℤ))
    (congrArg (ForgetEnrichment.of (Complex R)) hMN) rfl rfl rfl j j (HEq.refl _)
    _ _ hb
  have he := moduleHomPostcomposition_compose R D
    (S := ForgetEnrichment.of (Complex R) M)
    (M := dgCoherentBarFamily R D F ⟨n + 1, σ⟩)
    (N := dgCoherentBarFamily R D F (dgCoherentBarFace σ i.succ))
    (P := dgCoherentBarGraded R D F) j
    (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) M)
    (dgCoherentBarFaceBlock R D F σ i) (show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega)
  have hs : (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) N) j).f (-(n : ℤ))
      (moduleShiftInElement R D (n : ℤ) N) =
      (n : ℤ).negOnePow • dgCoherentBarShiftedInclusion R D F (dgCoherentBarFace σ i.succ) := by
    unfold dgCoherentBarShiftedInclusion
    simp only [dgCoherentBarFace, smul_smul, Int.units_mul_self, one_smul]
    rfl
  exact (heq_of_eq he).trans (hp.trans (heq_of_eq hs))

end SerrePositivity.InfinityCategories
