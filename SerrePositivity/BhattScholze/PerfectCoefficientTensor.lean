module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # B4-5：完全標数p係数環のテンソル

逆Frobeniusをテンソル積の普遍性で構成する。零環のテンソルも含む。
混標数の完備テンソルのperfectoid性は別工程。
-/

@[expose] public noncomputable section
universe u v w z
namespace SerrePositivity.BhattScholze
open scoped TensorProduct

/-- 係数テンソルの環射を、両因子の環射と基底上の一致から作る。
終域のR-代数構造を入力に要求せず、MathlibのAlgHom版へ接続する。 -/
def coefficientTensorLift {R : Type u} {A : Type v} {B : Type w} {D : Type z}
    [CommRing R] [CommRing A] [CommRing B] [CommRing D] [Algebra R A] [Algebra R B]
    (f : A →+* D) (g : B →+* D)
    (h : ∀ r : R, f (algebraMap R A r) = g (algebraMap R B r)) : A ⊗[R] B →+* D := by
  letI : Algebra R D := (f.comp (algebraMap R A)).toAlgebra
  let ff : A →ₐ[R] D := { f with commutes' := fun _ ↦ rfl }
  let gg : B →ₐ[R] D := { g with commutes' := fun r ↦ (h r).symm }
  exact (Algebra.TensorProduct.lift ff gg (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- 係数テンソル射の純粋テンソル上の式。 -/
theorem coefficientTensorLift_tmul {R : Type u} {A : Type v} {B : Type w} {D : Type z}
    [CommRing R] [CommRing A] [CommRing B] [CommRing D] [Algebra R A] [Algebra R B]
    (f : A →+* D) (g : B →+* D)
    (h : ∀ r : R, f (algebraMap R A r) = g (algebraMap R B r)) (a : A) (b : B) :
    coefficientTensorLift f g h (a ⊗ₜ[R] b) = f a * g b := rfl

/-- 完全係数環のテンソルの逆Frobenius候補を、両因子の逆Frobeniusから構成する。 -/
def perfectCoefficientTensorRoot (p : ℕ) [Fact p.Prime] (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [CharP R p] [CharP A p] [CharP B p]
    [PerfectRing R p] [PerfectRing A p] [PerfectRing B p] : A ⊗[R] B →+* A ⊗[R] B := by
  let K := A ⊗[R] B
  let iA : A →+* K :=
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
  let iB : B →+* K :=
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  have hiA (r : R) : iA (algebraMap R A r) = algebraMap R K r :=
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).commutes r
  have hiB (r : R) : iB (algebraMap R B r) = algebraMap R K r :=
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).commutes r
  let f := iA.comp (_root_.frobeniusEquiv A p).symm.toRingHom
  let g := iB.comp (_root_.frobeniusEquiv B p).symm.toRingHom
  have h : ∀ r : R, f (algebraMap R A r) = g (algebraMap R B r) := by
    intro r
    change iA ((_root_.frobeniusEquiv A p).symm (algebraMap R A r)) =
      iB ((_root_.frobeniusEquiv B p).symm (algebraMap R B r))
    rw [← (algebraMap R A).map_frobeniusEquiv_symm p,
      ← (algebraMap R B).map_frobeniusEquiv_symm p, hiA, hiB]
  exact coefficientTensorLift f g h

variable (p : ℕ) [Fact p.Prime] (R A B : Type u)
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [CharP R p] [CharP A p] [CharP B p]
variable [PerfectRing R p] [PerfectRing A p] [PerfectRing B p]

/-- 逆Frobenius候補の純粋テンソル上の式。 -/
theorem perfectCoefficientTensorRoot_tmul (a : A) (b : B) :
    perfectCoefficientTensorRoot p R A B (a ⊗ₜ[R] b) =
      (_root_.frobeniusEquiv A p).symm a ⊗ₜ[R] (_root_.frobeniusEquiv B p).symm b := by
  rw [perfectCoefficientTensorRoot, coefficientTensorLift_tmul]
  change ((_root_.frobeniusEquiv A p).symm a ⊗ₜ[R] (1 : B)) *
      ((1 : A) ⊗ₜ[R] (_root_.frobeniusEquiv B p).symm b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- 完全標数p環の任意の係数テンソル積は完全。テンソル積が零環になる場合も含む。 -/
theorem perfectCoefficientTensor_perfectRing : PerfectRing (A ⊗[R] B) p := by
  let K := A ⊗[R] B
  rcases subsingleton_or_nontrivial K with hs | hn
  · let := hs
    exact ⟨⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun x ↦ ⟨0, Subsingleton.elim _ x⟩⟩⟩
  · let := hn
    have hp : (p : K) = 0 := by
      rw [← map_natCast (algebraMap R K), CharP.cast_eq_zero, map_zero]
    let : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    let r := perfectCoefficientTensorRoot p R A B
    have hr : ∀ x : K, frobenius K p (r x) = x := by
      intro x
      refine TensorProduct.inductionOn x (fun a b ↦ ?_) (fun x y hx hy ↦ ?_)
      · change (r (a ⊗ₜ[R] b)) ^ p = a ⊗ₜ[R] b
        rw [perfectCoefficientTensorRoot_tmul, Algebra.TensorProduct.tmul_pow,
          frobeniusEquiv_symm_pow_p, frobeniusEquiv_symm_pow_p]
      · simp only [map_add, hx, hy]
    have hl : ∀ x : K, r (frobenius K p x) = x := by
      intro x
      refine TensorProduct.inductionOn x (fun a b ↦ ?_) (fun x y hx hy ↦ ?_)
      · change r ((a ⊗ₜ[R] b) ^ p) = a ⊗ₜ[R] b
        rw [Algebra.TensorProduct.tmul_pow, perfectCoefficientTensorRoot_tmul,
          frobeniusEquiv_symm_pow, frobeniusEquiv_symm_pow]
      · simp only [map_add, hx, hy]
    exact ⟨⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩⟩

end SerrePositivity.BhattScholze
