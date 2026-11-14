module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarShiftedInclusions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarShiftBlockInclusion
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

private lemma shiftBlock_comp_in_degree (s t : ℤ) {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R D} {q k c : ℤ}
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N).X q) (hk : s + q - t = k)
    (hl : -s + k = c) (hr : q + -t = c) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := M) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) (z := _root_.SerrePositivity.DifferentialGraded.shiftModule t N)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D s t f hk) (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D s M) hl =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := M) (y := N) (z := _root_.SerrePositivity.DifferentialGraded.shiftModule t N)
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D t N) f hr := by
  cases hr
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleShiftBlock_comp_shiftIn R D s t f hk

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixColumn_comp_shiftIn {n : ℕ} (σ : I _⦋n⦌) (k : ℕ)
    (h : k + 1 ≤ n) :
    compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, σ⟩)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, σ⟩))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F σ k h)
      (moduleShiftInElement R D (n : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, σ⟩))
      (show -(n : ℤ) + 1 = 1 - (n : ℤ) by omega) =
    compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, σ⟩)
      (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail σ (k + 1) h))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (((n - (k + 1) : ℕ) : ℤ).negOnePow •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail σ (k + 1) h))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F σ k h)
      (show -(k : ℤ) + -((n - (k + 1) : ℕ) : ℤ) = 1 - (n : ℤ) by omega) := by
  let M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, σ⟩
  let N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail σ (k + 1) h)
  let j := Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail σ (k + 1) h)
  have hb := shiftBlock_comp_in_degree R D (n : ℤ) ((n - (k + 1) : ℕ) : ℤ)
    (M := M) (N := N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F σ k h)
    (by omega : (n : ℤ) + -(k : ℤ) - ((n - (k + 1) : ℕ) : ℤ) = 1)
    (show -(n : ℤ) + 1 = 1 - (n : ℤ) by omega) (by omega)
  have he := _root_.SerrePositivity.DifferentialGraded.moduleHomPostcomposition_compose R D
    (S := ForgetEnrichment.of (Complex R) M) (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, σ⟩)
    (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail σ (k + 1) h))
    (P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) j
    (moduleShiftInElement R D (n : ℤ) M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F σ k h)
    (show -(n : ℤ) + 1 = 1 - (n : ℤ) by omega)
  have hp := congrArg
    ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M) j).f (1 - (n : ℤ))) hb
  have hr := _root_.SerrePositivity.DifferentialGraded.moduleHomPostcomposition_compose R D
    (S := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M) (M := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
    (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail σ (k + 1) h))
    (P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) j (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F σ k h)
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D ((n - (k + 1) : ℕ) : ℤ) N)
    (show -(k : ℤ) + -((n - (k + 1) : ℕ) : ℤ) = 1 - (n : ℤ) by omega)
  have hs : (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N) j).f
      (-((n - (k + 1) : ℕ) : ℤ)) (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D ((n - (k + 1) : ℕ) : ℤ) N) =
      ((n - (k + 1) : ℕ) : ℤ).negOnePow •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail σ (k + 1) h) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail, smul_smul, Int.units_mul_self, one_smul]
    rfl
  have hs' := congrArg (fun z => _root_.SerrePositivity.DifferentialGraded.compose R (x := M) (y := N)
    (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F σ k h)
    (show -(k : ℤ) + -((n - (k + 1) : ℕ) : ℤ) = 1 - (n : ℤ) by omega)) hs
  exact he.trans (hp.trans (hr.symm.trans hs'))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
