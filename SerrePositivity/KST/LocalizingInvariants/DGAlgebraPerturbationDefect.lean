module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPerturbedMultiplication

/-!
概要：追加微分の Leibniz 則を、その双加法的な差の零性へ帰着する。
方針：斉次 tensor 上の差を作り、各変数の加法性と零性から derivation 則を回収する。
規約：符号は左の次数。使われ方：cone の作用素を直和の四成分で検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.AlgebraPerturbation
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (θ : Cochain A.X A.X 1)

def defect (p q : ℤ) (a : A.X.X p) (b : A.X.X q) : A.X.X (p + q + 1) :=
  θ.v (p + q) (p + q + 1) rfl
    (μ[A.X].f (p + q) (ιTensorObj A.X A.X p q (p + q) rfl (a ⊗ₜ[R] b))) -
  (μ[A.X].f (p + q + 1) (ιTensorObj A.X A.X (p + 1) q (p + q + 1) (by omega)
    (θ.v p (p + 1) rfl a ⊗ₜ[R] b)) +
  p.negOnePow • μ[A.X].f (p + q + 1)
    (ιTensorObj A.X A.X p (q + 1) (p + q + 1) (by omega)
      (a ⊗ₜ[R] θ.v q (q + 1) rfl b)))

lemma defect_add_left (p q : ℤ) (a a' : A.X.X p) (b : A.X.X q) :
    defect A θ p q (a + a') b = defect A θ p q a b + defect A θ p q a' b := by
  simp only [defect, TensorProduct.add_tmul, map_add, smul_add]
  abel

lemma defect_add_right (p q : ℤ) (a : A.X.X p) (b b' : A.X.X q) :
    defect A θ p q a (b + b') = defect A θ p q a b + defect A θ p q a b' := by
  simp only [defect, TensorProduct.tmul_add, map_add, smul_add]
  abel

lemma isDerivation_iff_defect : IsDerivation A θ ↔
    ∀ (p q : ℤ) (a : A.X.X p) (b : A.X.X q), defect A θ p q a b = 0 := by
  constructor
  · intro h p q a b
    exact sub_eq_zero.mpr (h p q a b)
  · intro h p q a b
    exact sub_eq_zero.mp (h p q a b)

end SerrePositivity.KST.LocalizingInvariants.AlgebraPerturbation
