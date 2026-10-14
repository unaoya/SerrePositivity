module

public import SerrePositivity.CommutativeAlgebra.AdicFiniteGeneration
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # 有限なイデアル商から完備化の有限生成性へ

元の加群の有限性は要求しない。完備化の冪商を元の冪商に同定し、
前完備な基底環上の分離加群の有限生成判定を適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 有限生成イデアルの完備化の冪商は、元の加群の同じ冪商と同型。 -/
def adicCompletionQuotientEquiv (I : Ideal R) (hI : I.FG) (n : ℕ) :
    (AdicCompletion I M ⧸ I ^ n • (⊤ : Submodule R (AdicCompletion I M))) ≃ₗ[R]
      M ⧸ I ^ n • (⊤ : Submodule R M) :=
  (Submodule.quotEquivOfEq _ _ (AdicCompletion.pow_smul_top_eq_ker_eval hI)).trans
    ((AdicCompletion.eval I M n).quotKerEquivOfSurjective (AdicCompletion.eval_surjective I M n))

@[simp] theorem adicCompletionQuotientEquiv_mk (I : Ideal R) (hI : I.FG) (n : ℕ)
    (x : AdicCompletion I M) :
    adicCompletionQuotientEquiv I hI n (Submodule.Quotient.mk x) =
      AdicCompletion.eval I M n x := by
  simp [adicCompletionQuotientEquiv]

/-- 前完備な環上では、最初のイデアル商が有限なら完備化も有限。 -/
theorem moduleFinite_adicCompletion_of_finite_quotient (I : Ideal R) (hI : I.FG)
    [IsPrecomplete I R] [Module.Finite R (M ⧸ I • (⊤ : Submodule R M))] :
    Module.Finite R (AdicCompletion I M) := by
  let : IsAdicComplete I (AdicCompletion I M) := AdicCompletion.isAdicComplete hI
  let E : (AdicCompletion I M ⧸ I • (⊤ : Submodule R (AdicCompletion I M))) ≃ₗ[R]
      M ⧸ I • (⊤ : Submodule R M) := by
    have E := adicCompletionQuotientEquiv (M := M) I hI 1
    rw [pow_one] at E
    exact E
  let : Module.Finite R
      (AdicCompletion I M ⧸ I • (⊤ : Submodule R (AdicCompletion I M))) :=
    Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective
  obtain ⟨n, f, hf⟩ := exists_surjective_pi_of_finite_quotient (M := AdicCompletion I M) I
  exact Module.Finite.of_surjective f hf

end SerrePositivity
