module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # 拡張イデアルによる完備化と係数制限の比較

A のイデアル I を A 代数 S に拡張して取る完備化と、A 加群としての I 進完備化を
各冪商の同型から比較する。Noether 性・平坦性・局所性は不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open Submodule
variable {A S M : Type u} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
    (I : Ideal A)

/-- 各次数の冪商の、係数制限による同型。 -/
def adicCompletionScalarQuotientEquiv (n : ℕ) :
    (M ⧸ ((I.map (algebraMap A S)) ^ n • (⊤ : Submodule S M))) ≃ₗ[A]
      (M ⧸ (I ^ n • (⊤ : Submodule A M))) :=
  (Submodule.Quotient.restrictScalarsEquiv A _).symm.trans
    (Submodule.quotEquivOfEq _ _ (by
      rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq]
      simp))

@[simp] theorem adicCompletionScalarQuotientEquiv_mk (n : ℕ) (m : M) :
    adicCompletionScalarQuotientEquiv (S := S) I n (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk m := by
  simp [adicCompletionScalarQuotientEquiv]

/-- 冪商の比較は逆極限の遷移写像と両立する。 -/
theorem adicCompletionScalarQuotientEquiv_transition {m n : ℕ} (h : m ≤ n)
    (x : M ⧸ ((I.map (algebraMap A S)) ^ n • (⊤ : Submodule S M))) :
    adicCompletionScalarQuotientEquiv (S := S) I m
      (AdicCompletion.transitionMap (I.map (algebraMap A S)) M h x) =
    AdicCompletion.transitionMap I M h
      (adicCompletionScalarQuotientEquiv (S := S) I n x) := by
  induction x using Submodule.Quotient.induction_on
  simp [AdicCompletion.transitionMap, Submodule.factorPow]

/-- 拡張イデアルによる完備化と、基底のイデアルによる加群の完備化は A 線形同型。 -/
def adicCompletionScalarRestrictionEquiv :
    AdicCompletion (I.map (algebraMap A S)) M ≃ₗ[A] AdicCompletion I M where
  toFun x := ⟨fun n ↦ adicCompletionScalarQuotientEquiv (S := S) I n (x.val n), by
    intro m n h
    rw [← adicCompletionScalarQuotientEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n ↦ (adicCompletionScalarQuotientEquiv (S := S) I n).symm (x.val n), by
    intro m n h
    apply (adicCompletionScalarQuotientEquiv (S := S) I m).injective
    rw [adicCompletionScalarQuotientEquiv_transition]
    simp [x.property h]⟩
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    simp
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    simp
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    change adicCompletionScalarQuotientEquiv (S := S) I n (x.val n + y.val n) = _
    exact map_add _ _ _
  map_smul' a x := by
    apply AdicCompletion.ext
    intro n
    change adicCompletionScalarQuotientEquiv (S := S) I n (a • x.val n) = _
    exact map_smul _ _ _

/-- 係数制限の比較は元の加群からの標準写像を保つ。 -/
@[simp] theorem adicCompletionScalarRestrictionEquiv_of (m : M) :
    adicCompletionScalarRestrictionEquiv (S := S) I
      (AdicCompletion.of (I.map (algebraMap A S)) M m) = AdicCompletion.of I M m := by
  apply AdicCompletion.ext
  intro n
  exact adicCompletionScalarQuotientEquiv_mk (S := S) I n m

/-- 各次数の評価と比較が両立する。 -/
@[simp] theorem adicCompletionScalarRestrictionEquiv_eval (n : ℕ)
    (x : AdicCompletion (I.map (algebraMap A S)) M) :
    AdicCompletion.eval I M n (adicCompletionScalarRestrictionEquiv (S := S) I x) =
      adicCompletionScalarQuotientEquiv (S := S) I n
        (AdicCompletion.eval (I.map (algebraMap A S)) M n x) := rfl

end SerrePositivity
