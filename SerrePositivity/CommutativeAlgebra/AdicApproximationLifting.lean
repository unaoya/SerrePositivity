module

public import SerrePositivity.CommutativeAlgebra.AdicCompleteness

/-! # 次数のずれを許すadic近似から実際の像へ

各次数で誤差を一つ下げ、係数の次数が一様なずれで増加するなら、
完備な始域で係数の極限を取り、分離した終域で等式を得る。
終域の部分加群の完備性・有限性・閉性や環のNoether性は要求しない。
-/

public section
namespace SerrePositivity
variable {R P M : Type*} [CommRing R]
variable [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]

/-- 初期形式の生成から得られる一様な次数付き近似を、元の部分加群の生成へ持ち上げる。
cは生成元の次数の上界。次数nでの係数はI^(n-c)に入ることを要求する。 -/
theorem submodule_le_range_of_shifted_adic_approximation
    (I : Ideal R) [IsPrecomplete I P] [IsHausdorff I M]
    (f : P →ₗ[R] M) (N : Submodule R M) (hf : f.range ≤ N) (c : ℕ)
    (happrox : ∀ n x, x ∈ N → x ∈ I ^ n • (⊤ : Submodule R M) →
      ∃ p : P, p ∈ I ^ (n - c) • (⊤ : Submodule R P) ∧
        x - f p ∈ I ^ (n + 1) • (⊤ : Submodule R M)) : N ≤ f.range := by
  classical
  intro x hx
  let A (n : ℕ) := {p : P // x - f p ∈ N ∧ x - f p ∈ I ^ n • (⊤ : Submodule R M)}
  let step (n : ℕ) (p : A n) : A (n + 1) := by
    let H := happrox n (x - f p.val) p.property.1 p.property.2
    let q := Classical.choose H
    have hq := Classical.choose_spec H
    refine ⟨p.val + q, ?_, ?_⟩
    · rw [map_add, sub_add_eq_sub_sub]
      exact N.sub_mem p.property.1 (hf (LinearMap.mem_range_self f q))
    · simpa only [map_add, sub_add_eq_sub_sub] using hq.2
  let u : ∀ n, A n := fun n ↦ Nat.rec
    (show A 0 from ⟨0, by simpa using hx, by simp⟩) step n
  have hu_step (n : ℕ) : (u (n + 1)).val - (u n).val ∈
      I ^ (n - c) • (⊤ : Submodule R P) := by
    change (step n (u n)).val - (u n).val ∈ _
    change (u n).val + Classical.choose
      (happrox n (x - f (u n).val) (u n).property.1 (u n).property.2) - (u n).val ∈ _
    simpa only [add_sub_cancel_left] using (Classical.choose_spec
      (happrox n (x - f (u n).val) (u n).property.1 (u n).property.2)).1
  let v (n : ℕ) := (u (n + c)).val
  have hv_step (n : ℕ) : v (n + 1) - v n ∈ I ^ n • (⊤ : Submodule R P) := by
    have hidx : n + c + 1 = n + 1 + c := by omega
    exact Eq.mp (congrArg (fun t : ℕ ↦ (u t).val - (u (n + c)).val ∈
      I ^ n • (⊤ : Submodule R P)) hidx)
      (by simpa only [Nat.add_sub_cancel] using hu_step (n + c))
  have hv : ∀ m n, m ≤ n → v m ≡ v n [SMOD (I ^ m • (⊤ : Submodule R P))] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact SModEq.refl _
    | succ n hmn ih =>
      apply ih.trans
      exact (SModEq.sub_mem.mpr (hv_step n)).symm.mono
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) v (fun {m n} h ↦ hv m n h)
  refine ⟨L, ?_⟩
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  have herr : x ≡ f (v n) [SMOD (I ^ n • (⊤ : Submodule R M))] :=
    (SModEq.sub_mem.mpr (u (n + c)).property.2).mono
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c)))
  exact ((smodEq_map_pow I f (hL n)).symm.trans herr.symm)

/-- 前完備な環上の有限な係数加群で上の近似を供給すれば、部分加群は有限生成。
部分加群自体の閉性・前完備性・有限性を仮定しない。 -/
theorem fg_of_shifted_adic_approximation
    (I : Ideal R) [IsPrecomplete I R] [IsHausdorff I M] [Module.Finite R P]
    (f : P →ₗ[R] M) (N : Submodule R M) (hf : f.range ≤ N) (c : ℕ)
    (happrox : ∀ n x, x ∈ N → x ∈ I ^ n • (⊤ : Submodule R M) →
      ∃ p : P, p ∈ I ^ (n - c) • (⊤ : Submodule R P) ∧
        x - f p ∈ I ^ (n + 1) • (⊤ : Submodule R M)) : N.FG := by
  let : IsPrecomplete I P := isPrecomplete_finite I P
  have hN : N = f.range := le_antisymm
    (submodule_le_range_of_shifted_adic_approximation I f N hf c happrox) hf
  rw [hN]
  simpa only [Submodule.map_top] using (Module.Finite.fg_top (R := R) (M := P)).map f

end SerrePositivity
