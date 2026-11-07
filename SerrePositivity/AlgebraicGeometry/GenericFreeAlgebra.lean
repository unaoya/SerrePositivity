module

public import SerrePositivity.AlgebraicGeometry.GenericFreePolynomialQuotient
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
概要：整域上の有限型代数の一般自由性（Stacks 051R の代数の場合）。
方針：係数変更と商の比較で、多項式商の標準単項式基底を移す。
規約：自由性は局所化環上。多項式の関係イデアルに有限生成性を仮定しない。
使われ方：平坦化の一般平坦性と、05FS の射影性判定の局所化側。
-/

@[expose] public noncomputable section
universe u v w

namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：多変数多項式商のテンソル基底変更は、係数変更後の多項式を拡大イデアルで割った代数に同型。
方針：Mathlib のテンソルと商の比較、および多項式の係数変更の比較を合成する。
規約：係数変更の平坦性や変数の有限性は不要。
使われ方：多項式商の局所化上の自由性を、元の商の局所化に移す。
-/
def mvPolynomialQuotientTensorEquiv
    {R : Type u} {C : Type v} {σ : Type w} [CommRing R] [CommRing C] [Algebra R C]
    (I : Ideal (MvPolynomial σ R)) :
    C ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[C]
      MvPolynomial σ C ⧸ I.map (MvPolynomial.map (algebraMap R C)) := by
  let e : C ⊗[R] MvPolynomial σ R ≃ₐ[C] MvPolynomial σ C :=
    MvPolynomial.algebraTensorAlgEquiv R C
  let e₀ : (C ⊗[R] MvPolynomial σ R) →+* MvPolynomial σ C := e
  let ι : MvPolynomial σ R →ₐ[R] C ⊗[R] MvPolynomial σ R :=
    Algebra.TensorProduct.includeRight
  let φ := MvPolynomial.map (σ := σ) (algebraMap R C)
  have h : e₀.comp ι.toRingHom = φ := by
    apply RingHom.ext
    intro x
    simp [e₀, e, ι, φ]
  have hI : I.map φ = (I.map ι.toRingHom).map e₀ := by
    rw [Ideal.map_map, h]
  let q := Algebra.TensorProduct.tensorQuotientEquiv (R := R) C (MvPolynomial σ R) C I
  exact q.trans (Ideal.quotientEquivAlg (I.map ι.toRingHom) (I.map φ) e hI)

/--
概要：整域上の有限型代数は、ある非零元を反転すると基底環上自由。
方針：有限変数多項式環からの全射を商表示に直し、係数変更後の標準単項式基底を移す。
規約：自由性の対象は通常のテンソル積。有限階数は仮定しない。
使われ方：Stacks 051R の有限型代数の場合と、05FS の一般自由性の入力。
-/
theorem exists_nonzero_free_localization_of_finiteType
    (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] :
    ∃ f : R, f ≠ 0 ∧ Module.Free (Localization.Away f) (Localization.Away f ⊗[R] B) := by
  classical
  obtain ⟨σ, hσ, π, hπ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial' (R := R) (S := B)).mp inferInstance
  let : Fintype σ := hσ
  let order := Fintype.equivFin σ
  let : LinearOrder σ := LinearOrder.lift' order order.injective
  let : WellFoundedGT σ := Finite.to_wellFoundedGT
  let I := RingHom.ker π.toRingHom
  obtain ⟨f, hf, hfree⟩ :=
    exists_nonzero_free_polynomial_quotient_localization MonomialOrder.lex I
  let C := Localization.Away f
  let e : (MvPolynomial σ R ⧸ I) ≃ₐ[R] B := Ideal.quotientKerAlgEquivOfSurjective hπ
  refine ⟨f, hf, Module.Free.of_equiv' hfree ?_⟩
  exact ((mvPolynomialQuotientTensorEquiv (C := C) I).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[C] C) e)).toLinearEquiv

end SerrePositivity.AlgebraicGeometry
