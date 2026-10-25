module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarShiftedInclusions
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarShiftBlockInclusion
public import SerrePositivity.DifferentialGraded.Module.HomPostcompositionComposition

/-!
概要：元の prefix 列とシフト包含の合成を、同じ tail 包含と元の高次射の合成へ戻す。
方針：shift 対の消去と閉余積包含との結合則を使う。
規約：元の prefix の全次数係数と tail ラベルを保持する。
使われ方：実 bar の θ 作用と HA 右辺の合成項の一項ごとの比較。
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

private lemma shiftBlock_comp_in_degree (s t : ℤ) {M N : RightModule R D} {q k c : ℤ}
    (f : (moduleHom R D M N).X q) (hk : s + q - t = k)
    (hl : -s + k = c) (hr : q + -t = c) :
    compose R (x := M) (y := shiftModule s M) (z := shiftModule t N)
      (moduleHomShiftBlock R D s t f hk) (moduleShiftInElement R D s M) hl =
    compose R (x := M) (y := N) (z := shiftModule t N)
      (moduleShiftInElement R D t N) f hr := by
  cases hr
  exact dgModuleShiftBlock_comp_shiftIn R D s t f hk

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixColumn_comp_shiftIn {n : ℕ} (σ : I _⦋n⦌) (k : ℕ)
    (h : k + 1 ≤ n) :
    compose R (x := dgCoherentBarSource R D F ⟨n, σ⟩)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, σ⟩))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarPrefixColumn R D F σ k h)
      (moduleShiftInElement R D (n : ℤ) (dgCoherentBarSource R D F ⟨n, σ⟩))
      (show -(n : ℤ) + 1 = 1 - (n : ℤ) by omega) =
    compose R (x := dgCoherentBarSource R D F ⟨n, σ⟩)
      (y := dgCoherentBarSource R D F (dgCoherentBarTail σ (k + 1) h))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (((n - (k + 1) : ℕ) : ℤ).negOnePow •
        dgCoherentBarShiftedInclusion R D F (dgCoherentBarTail σ (k + 1) h))
      (dgCoherentBarPrefixHom R D F σ k h)
      (show -(k : ℤ) + -((n - (k + 1) : ℕ) : ℤ) = 1 - (n : ℤ) by omega) := by
  let M := dgCoherentBarSource R D F ⟨n, σ⟩
  let N := dgCoherentBarSource R D F (dgCoherentBarTail σ (k + 1) h)
  let j := Sigma.ι (dgCoherentBarFamily R D F) (dgCoherentBarTail σ (k + 1) h)
  have hb := shiftBlock_comp_in_degree R D (n : ℤ) ((n - (k + 1) : ℕ) : ℤ)
    (M := M) (N := N) (dgCoherentBarPrefixHom R D F σ k h)
    (by omega : (n : ℤ) + -(k : ℤ) - ((n - (k + 1) : ℕ) : ℤ) = 1)
    (show -(n : ℤ) + 1 = 1 - (n : ℤ) by omega) (by omega)
  have he := moduleHomPostcomposition_compose R D
    (S := ForgetEnrichment.of (Complex R) M) (M := dgCoherentBarFamily R D F ⟨n, σ⟩)
    (N := dgCoherentBarFamily R D F (dgCoherentBarTail σ (k + 1) h))
    (P := dgCoherentBarGraded R D F) j
    (moduleShiftInElement R D (n : ℤ) M) (dgCoherentBarPrefixBlock R D F σ k h)
    (show -(n : ℤ) + 1 = 1 - (n : ℤ) by omega)
  have hp := congrArg
    ((eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) M) j).f (1 - (n : ℤ))) hb
  have hr := moduleHomPostcomposition_compose R D
    (S := ForgetEnrichment.of (Complex R) M) (M := ForgetEnrichment.of (Complex R) N)
    (N := dgCoherentBarFamily R D F (dgCoherentBarTail σ (k + 1) h))
    (P := dgCoherentBarGraded R D F) j (dgCoherentBarPrefixHom R D F σ k h)
    (moduleShiftInElement R D ((n - (k + 1) : ℕ) : ℤ) N)
    (show -(k : ℤ) + -((n - (k + 1) : ℕ) : ℤ) = 1 - (n : ℤ) by omega)
  have hs : (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) N) j).f
      (-((n - (k + 1) : ℕ) : ℤ)) (moduleShiftInElement R D ((n - (k + 1) : ℕ) : ℤ) N) =
      ((n - (k + 1) : ℕ) : ℤ).negOnePow •
        dgCoherentBarShiftedInclusion R D F (dgCoherentBarTail σ (k + 1) h) := by
    unfold dgCoherentBarShiftedInclusion
    simp only [dgCoherentBarTail, smul_smul, Int.units_mul_self, one_smul]
    rfl
  have hs' := congrArg (fun z => compose R (x := M) (y := N)
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    z (dgCoherentBarPrefixHom R D F σ k h)
    (show -(k : ℤ) + -((n - (k + 1) : ℕ) : ℤ) = 1 - (n : ℤ) by omega)) hs
  exact he.trans (hp.trans (hr.symm.trans hs'))

end SerrePositivity.InfinityCategories
