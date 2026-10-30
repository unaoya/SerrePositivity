module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # 完全環の被約性・根基イデアル・係数テンソル

## 概要

指数が 1 より大きい冪写像が全単射な環は被約である。冪写像が全射な環では根基イデアルは冪等で、完全環では余接空間が消える。完全標数 p の係数環のテンソル積は完全である（逆 Frobenius をテンソル積の普遍性で作る、`coefficientTensorLift`）。

## 方針

被約性は冪写像の単射性から、冪等性は元の根を取って積に分けることから示す。テンソル積は零環の場合も含めて扱う。

## 規約

`coefficientTensorLift` は BhattScholze が名前で参照する。混標数の完備テンソルの perfectoid 性は扱わない。完全環のテンソル積の `PerfectRing` instance は Mathlib への提出候補。

## 使われ方

BhattScholze の perfect prism のテンソル、`Perfectoid/Fontaine`。
-/

@[expose] public noncomputable section

universe u v w z

section PerfectPowerReducedPart

namespace SerrePositivity

/-- No characteristic or nontriviality hypothesis is needed, including for zero quotients. -/
lemma isReduced_of_perfectPower (R : Type u) [CommRing R] (p : ℕ)
    [PerfectRing R p] (hp : 1 < p) : IsReduced R :=
  (isReduced_iff_pow_one_lt p hp).mpr (by
    intro x hx
    exact (PerfectRing.bijective_frobenius (R := R) (p := p)).injective
      (by simpa only [zero_pow (by omega : p ≠ 0)] using hx))

end SerrePositivity

end PerfectPowerReducedPart

section PerfectRadicalIdealPart

namespace SerrePositivity
variable (R : Type u) [CommRing R] (I : Ideal R)

/-- A radical ideal is idempotent when every element admits an n-th root, n≥2. -/
lemma radicalIdeal_idempotent_of_power_surjective (n : ℕ) (hn : 2 ≤ n)
    (hroot : ∀ x : R, ∃ y : R, y ^ n = x) (hI : I.IsRadical) : IsIdempotentElem I := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  obtain ⟨y, hy⟩ := hroot x
  have hyI : y ∈ I := hI ⟨n, by simpa only [hy] using hx⟩
  have hyN : y ^ (n - 1) ∈ I := I.pow_mem_of_mem hyI _ (by omega)
  have he : y * y ^ (n - 1) = x := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega), hy]
  rw [← he]
  exact Ideal.mul_mem_mul hyI hyN

/-- In a perfect characteristic-p ring, every radical ideal is idempotent. -/
lemma radicalIdeal_idempotent_of_perfectRing (p : ℕ) [Fact p.Prime]
    [CharP R p] [PerfectRing R p] (hI : I.IsRadical) : IsIdempotentElem I :=
  radicalIdeal_idempotent_of_power_surjective R I p (Fact.out : p.Prime).two_le
    (fun x => ⟨(frobeniusEquiv R p).symm x, frobeniusEquiv_symm_pow_p R p x⟩) hI

end SerrePositivity

end PerfectRadicalIdealPart

section PerfectCoefficientTensorPart

namespace SerrePositivity
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

end SerrePositivity

end PerfectCoefficientTensorPart
