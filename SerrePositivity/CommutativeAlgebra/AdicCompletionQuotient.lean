module

public import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # 有限生成イデアルの完備化と冪商

完備化の評価の核を計算し、全ての冪商を元の環の冪商へ同定する。
環のNoether性は不要。n=0では両辺とも零環である。
-/

@[expose] public section
namespace SerrePositivity
variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
include hI

/-- 有限生成イデアルに沿う完備化のn段評価の核。 -/
theorem adicCompletion_ker_eval_eq_map (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  trans x ∈ (AdicCompletion.eval I R n).ker
  · change (Ideal.quotientEquivAlgOfEq R
      (show (I ^ n • ⊤ : Ideal R) = I ^ n from by ext; simp))
        (AdicCompletion.eval I R n x) = 0 ↔ AdicCompletion.eval I R n x = 0
    exact map_eq_zero_iff _ (AlgEquiv.injective _)
  · simp [← AdicCompletion.pow_smul_top_eq_ker_eval hI]

/-- 完備化に拡張したイデアルのn乗が評価の核となる。 -/
theorem adicCompletion_ker_eval_eq_pow_map (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  rw [adicCompletion_ker_eval_eq_map I hI, Ideal.map_pow]

/-- 完備化の冪商と元の環の冪商の係数を保つ同型。 -/
noncomputable def adicCompletionPowQuotientEquiv (n : ℕ) :
    (AdicCompletion I R ⧸ ((I.map (algebraMap R (AdicCompletion I R))) ^ n)) ≃ₐ[R]
      (R ⧸ (I ^ n)) :=
  (Ideal.quotientEquivAlgOfEq R (adicCompletion_ker_eval_eq_pow_map I hI n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.surjective_evalₐ I n))

/-- 同型は完備化の代表元をそのn段評価へ送る。 -/
@[simp] theorem adicCompletionPowQuotientEquiv_mk (n : ℕ) (x : AdicCompletion I R) :
    adicCompletionPowQuotientEquiv I hI n (Ideal.Quotient.mk _ x) =
      AdicCompletion.evalₐ I n x := by
  with_unfolding_all
    change (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.surjective_evalₐ I n))
      ((Ideal.quotientEquivAlgOfEq R (adicCompletion_ker_eval_eq_pow_map I hI n).symm)
        (Ideal.Quotient.mk _ x)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk _ x

/-- 元の環からの係数写像との両立を、代表元で確認する。 -/
@[simp] theorem adicCompletionPowQuotientEquiv_algebraMap (n : ℕ) (x : R) :
    adicCompletionPowQuotientEquiv I hI n
      (Ideal.Quotient.mk _ (algebraMap R (AdicCompletion I R) x)) =
        Ideal.Quotient.mk (I ^ n) x := by
  rw [adicCompletionPowQuotientEquiv_mk, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of]
  simp

end SerrePositivity
