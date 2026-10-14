module

public import SerrePositivity.CommutativeAlgebra.PrincipalAdicFaithfulDescent
public import SerrePositivity.CommutativeAlgebra.PerfectoidUntiltNaturality
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # B4-5：G1の剰余テンソルと通常テンソルのmod p

G1と同じ剰余代数構造を使い、Mathlibの基底変更の消去と商テンソルの同型を合成する。
導来テンソルやTorの仮定を使わない通常テンソルの比較。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] principalAdicQuotientAlgebra
variable (p : ℕ) (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- G1の正確な剰余テンソルを、通常テンソルをpで割った商へ同定する。 -/
def tensorResidueBaseChangeEquiv :
    ((R ⧸ Ideal.span {(p : R)}) ⊗[R] T) ⊗[R ⧸ Ideal.span {(p : R)}]
      (S ⧸ Ideal.span {algebraMap R S (p : R)}) ≃+*
      (S ⊗[R] T) ⧸ Ideal.span {(p : S ⊗[R] T)} := by
  let Q := R ⧸ Ideal.span {(p : R)}
  let U := S ⧸ Ideal.span {algebraMap R S (p : R)}
  let e1 := (Algebra.TensorProduct.comm Q (Q ⊗[R] T) U).toRingEquiv
  let : IsScalarTower R Q U := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let e2 := (Algebra.TensorProduct.cancelBaseChange R Q Q U T).toRingEquiv
  let e3 := (Algebra.TensorProduct.quotientTensorEquiv (R := R) R T S
    (Ideal.span {algebraMap R S (p : R)})).toRingEquiv
  have hI : (Ideal.span {algebraMap R S (p : R)}).map (algebraMap S (S ⊗[R] T)) =
      Ideal.span {(p : S ⊗[R] T)} := by
    simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  exact e1.trans (e2.trans (e3.trans (Ideal.quotEquivOfEq hI)))

/-- 比較同型の純粋テンソルの代表元上の式。 -/
@[simp] theorem tensorResidueBaseChangeEquiv_tmul_mk (r : R) (s : S) (t : T) :
    tensorResidueBaseChangeEquiv p R S T
      ((Ideal.Quotient.mk _ r ⊗ₜ[R] t) ⊗ₜ[R ⧸ Ideal.span {(p : R)}]
        Ideal.Quotient.mk _ s) =
      Ideal.Quotient.mk _ ((algebraMap R S r * s) ⊗ₜ[R] t) := by
  simp [tensorResidueBaseChangeEquiv, Algebra.smul_def]
  rfl

variable {C : Type u} [CommRing C] [Algebra R C]

/-- 比較同型はG1の線形テンソル射と通常テンソルの標準mod p射を結ぶ。 -/
theorem tensorResidueBaseChangeEquiv_natural [Fact p.Prime] (f : S →ₐ[R] C)
    (x : ((R ⧸ Ideal.span {(p : R)}) ⊗[R] T) ⊗[R ⧸ Ideal.span {(p : R)}]
      (S ⧸ Ideal.span {algebraMap R S (p : R)})) :
    tensorResidueBaseChangeEquiv p R C T
      (((principalAdicReductionMap (p : R) f).lTensor
        ((R ⧸ Ideal.span {(p : R)}) ⊗[R] T)) x) =
      modPMap p (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom
        (tensorResidueBaseChangeEquiv p R S T x) := by
  refine TensorProduct.inductionOn x (fun e s ↦ ?_) (fun x y hx hy ↦ ?_)
  · refine TensorProduct.inductionOn e (fun r t ↦ ?_) (fun e e' he he' ↦ ?_)
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
      rw [LinearMap.lTensor_tmul, principalAdicReductionMap_mk,
        tensorResidueBaseChangeEquiv_tmul_mk, tensorResidueBaseChangeEquiv_tmul_mk]
      change Ideal.Quotient.mk _ ((algebraMap R C r * f s) ⊗ₜ[R] t) =
        Ideal.Quotient.mk _ (f (algebraMap R S r * s) ⊗ₜ[R] t)
      rw [map_mul, f.commutes]
    · simp only [TensorProduct.add_tmul, map_add, he, he']
  · simp only [map_add, hx, hy]

/-- 通常テンソルのmod p全射性を、G1の正確な剰余テンソル線形射へ移す。 -/
theorem surjective_principalResidueTensor_of_modP_tensorMap [Fact p.Prime]
    (f : S →ₐ[R] C)
    (h : Function.Surjective
      (modPMap p (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom)) :
    Function.Surjective ((principalAdicReductionMap (p : R) f).lTensor
      ((R ⧸ Ideal.span {(p : R)}) ⊗[R] T)) := by
  intro y
  obtain ⟨x, hx⟩ := h (tensorResidueBaseChangeEquiv p R C T y)
  refine ⟨(tensorResidueBaseChangeEquiv p R S T).symm x,
    (tensorResidueBaseChangeEquiv p R C T).injective ?_⟩
  rw [tensorResidueBaseChangeEquiv_natural,
    (tensorResidueBaseChangeEquiv p R S T).apply_symm_apply]
  exact hx

end SerrePositivity.BhattScholze
