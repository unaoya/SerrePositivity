module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-! # 導分によるイデアル冪の次数降下

Leibniz則から δ(I^(n+1)) ⊆ I^n M を証明する。
冪級数・位相・有限生成性はこの代数的評価には要求しない。
-/

@[expose] public section
namespace SerrePositivity

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M]

/-- 導分はイデアル冪の次数を高々一つ下げる。 -/
theorem derivation_mem_pow_smul (δ : Derivation R S M) (I : Ideal S) (n : ℕ)
    {x : S} (hx : x ∈ I ^ (n + 1)) : δ x ∈ I ^ n • (⊤ : Submodule S M) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
    · rw [δ.leibniz]
      apply Submodule.add_mem
      · rw [pow_succ', Submodule.mul_smul]
        exact Submodule.smul_mem_smul ha (ih hb)
      · exact Submodule.smul_mem_smul hb Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ ha hb

end SerrePositivity
