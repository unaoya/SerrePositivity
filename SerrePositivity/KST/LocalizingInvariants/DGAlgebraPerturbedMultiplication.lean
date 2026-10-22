module

public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Complexes.Composition
public import SerrePositivity.DifferentialGraded.Complexes.UnitScalarEvaluation
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroAlgebra

/-!
概要：閉じた平方零の次数一 derivation で微分を変えても、元の積は鎖写像となる。
方針：元の積の Leibniz 則と追加微分の Leibniz 則を、斉次 tensor 上で加える。
規約：derivation 則は作用素の具体的な性質として検証する。使われ方：Postnikov cone。
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
  (hθ : δ 1 2 θ = 0) (hθθ : θ.comp θ (rfl : (1 : ℤ) + 1 = 2) = 0)

abbrev obj : Complex R := perturbComplex A.X θ hθ hθθ

def IsDerivation : Prop := ∀ (p q : ℤ) (a : A.X.X p) (b : A.X.X q),
  θ.v (p + q) (p + q + 1) rfl
    (μ[A.X].f (p + q) (ιTensorObj A.X A.X p q (p + q) rfl (a ⊗ₜ[R] b))) =
  μ[A.X].f (p + q + 1) (ιTensorObj A.X A.X (p + 1) q (p + q + 1) (by omega)
    (θ.v p (p + 1) rfl a ⊗ₜ[R] b)) +
  p.negOnePow • μ[A.X].f (p + q + 1)
    (ιTensorObj A.X A.X p (q + 1) (p + q + 1) (by omega)
      (a ⊗ₜ[R] θ.v q (q + 1) rfl b))

variable (hd : IsDerivation A θ)

include hd in
lemma mul_d_apply (p q : ℤ) (a : A.X.X p) (b : A.X.X q) :
    (obj A θ hθ hθθ).d (p + q) (p + q + 1)
      (μ[A.X].f (p + q) (ιTensorObj A.X A.X p q (p + q) rfl (a ⊗ₜ[R] b))) =
    μ[A.X].f (p + q + 1) (ιTensorObj A.X A.X (p + 1) q (p + q + 1) (by omega)
      ((obj A θ hθ hθθ).d p (p + 1) a ⊗ₜ[R] b)) +
    p.negOnePow • μ[A.X].f (p + q + 1)
      (ιTensorObj A.X A.X p (q + 1) (p + q + 1) (by omega)
        (a ⊗ₜ[R] (obj A θ hθ hθθ).d q (q + 1) b)) := by
  have hi := ConcreteCategory.congr_hom (μ[A.X].comm (p + q) (p + q + 1))
    (ιTensorObj A.X A.X p q (p + q) rfl (a ⊗ₜ[R] b))
  change A.X.d (p + q) (p + q + 1) (_ : A.X.X (p + q)) =
    μ[A.X].f (p + q + 1) ((A.X ⊗ A.X).d (p + q) (p + q + 1)
      (ιTensorObj A.X A.X p q (p + q) rfl (a ⊗ₜ[R] b))) at hi
  have ht := SerrePositivity.cochainTensor_d_apply_ι A.X A.X p q (p + q) rfl a b
  have hi' := hi.trans (congrArg (fun v : (A.X ⊗ A.X).X (p + q + 1) =>
    μ[A.X].f (p + q + 1) v) ht)
  rw [map_add, chain_units_smul] at hi'
  simp only [obj, perturbComplex_d, ModuleCat.hom_add, LinearMap.add_apply]
  change A.X.d (p + q) (p + q + 1) _ + θ.v (p + q) (p + q + 1) rfl _ = _
  exact (congrArg₂ (· + ·) hi' (hd p q a b)).trans (by
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, smul_add]
    exact add_add_add_comm _ _ _ _)

def mul : obj A θ hθ hθθ ⊗ obj A θ hθ hθθ ⟶ obj A θ hθ hθθ :=
  tensorLift (fun p q n h => ιTensorObj A.X A.X p q n h ≫ μ[A.X].f n) (fun p q => by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a b
    exact mul_d_apply A θ hθ hθθ hd p q a b)

lemma mul_ι (p q n : ℤ) (h : p + q = n) :
    ιTensorObj (obj A θ hθ hθθ) (obj A θ hθ hθθ) p q n h ≫ (mul A θ hθ hθθ hd).f n =
      ιTensorObj A.X A.X p q n h ≫ μ[A.X].f n := ι_tensorLift _ _ p q n h

lemma mul_apply (p q n : ℤ) (h : p + q = n) (a : A.X.X p) (b : A.X.X q) :
    (mul A θ hθ hθθ hd).f n
      (ιTensorObj (obj A θ hθ hθθ) (obj A θ hθ hθθ) p q n h (a ⊗ₜ[R] b)) =
        μ[A.X].f n (ιTensorObj A.X A.X p q n h (a ⊗ₜ[R] b)) :=
  ConcreteCategory.congr_hom (mul_ι A θ hθ hθθ hd p q n h) (a ⊗ₜ[R] b)

end SerrePositivity.KST.LocalizingInvariants.AlgebraPerturbation
