module

public import SerrePositivity.GroupTheory.Coxeter.TypeA

/-! # 隣接互換による有限対称群の帰納

型Aと対称群の同型を介して、Coxeter系の単純生成元による帰納を再利用する。
-/

@[expose] public section

namespace SerrePositivity.Coxeter

/-- 恒等置換と、右から隣接互換を掛ける段階による有限対称群の帰納。 -/
lemma permutation_induction_right {n : ℕ} {p : Equiv.Perm (Fin (n + 1)) → Prop}
    (σ : Equiv.Perm (Fin (n + 1))) (hone : p 1)
    (hstep : ∀ σ i, p σ → p (σ * adjacentTransposition i)) : p σ := by
  have h : ∀ w : (CoxeterMatrix.A n).Group, p (typeAEquivPerm n w) := by
    intro w
    apply (CoxeterMatrix.A n).toCoxeterSystem.simple_induction_right w
    · simpa only [map_one] using hone
    · intro w i hw
      rw [map_mul]
      erw [typeAEquivPerm_simple]
      exact hstep _ i hw
  simpa only [MulEquiv.apply_symm_apply] using h ((typeAEquivPerm n).symm σ)

end SerrePositivity.Coxeter
