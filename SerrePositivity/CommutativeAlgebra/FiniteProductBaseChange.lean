module

public import Mathlib.RingTheory.TensorProduct.Pi

/-! # 有限直積の元の係数を保つ通常の底変換

mathlib の tensor と有限直積の比較を、係数環を左に置く元の底変換へ正規化する。
perfectoid 性・平坦性・完備性は不要。
-/

@[expose] public noncomputable section
universe u v w z
namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    {ι : Type w} [Finite ι] (B : ι → Type z) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

/-- 左係数の有限直積を各底変換の直積へ移す、元の係数環上の代数同型。 -/
def finiteProductBaseChangeEquiv :
    ((i : ι) → B i) ⊗[R] S ≃ₐ[(i : ι) → B i] (i : ι) → B i ⊗[R] S := by
  classical
  letI := Fintype.ofFinite ι
  let e := (Algebra.TensorProduct.comm R ((i : ι) → B i) S).trans
    ((Algebra.TensorProduct.piRight R R S B).trans
      (AlgEquiv.piCongrRight (fun i => Algebra.TensorProduct.comm R S (B i))))
  refine AlgEquiv.ofRingEquiv (f := e.toRingEquiv) ?_
  intro b
  change e (b ⊗ₜ[R] (1 : S)) = fun i => b i ⊗ₜ[R] (1 : S)
  ext i
  simp only [e, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.piRight_tmul, AlgEquiv.piCongrRight_apply]

/-- 全ての純 tensor の各成分をそのまま保つ。 -/
@[simp] theorem finiteProductBaseChangeEquiv_tmul
    (b : (i : ι) → B i) (s : S) (i : ι) :
    finiteProductBaseChangeEquiv R S B (b ⊗ₜ[R] s) i = b i ⊗ₜ[R] s := by
  classical
  simp only [finiteProductBaseChangeEquiv, AlgEquiv.ofRingEquiv_apply, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.piRight_tmul, AlgEquiv.piCongrRight_apply]

/-- 元の S からの標準底変換写像は、各成分の同じ標準写像となる。 -/
@[simp] theorem finiteProductBaseChangeEquiv_unit (s : S) (i : ι) :
    finiteProductBaseChangeEquiv R S B ((1 : (i : ι) → B i) ⊗ₜ[R] s) i =
      (1 : B i) ⊗ₜ[R] s :=
  finiteProductBaseChangeEquiv_tmul R S B 1 s i

variable {C : ι → Type z} [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)]

/-- 有限直積の元の各代数写像による底変換と、標準比較の各座標は可換である。 -/
theorem finiteProductBaseChangeEquiv_naturality
    (f : ∀ i, B i →ₐ[R] C i) (x : ((i : ι) → B i) ⊗[R] S) (i : ι) :
    finiteProductBaseChangeEquiv R S C
      (Algebra.TensorProduct.map
        (AlgHom.pi (fun j => (f j).comp (Pi.evalAlgHom R B j))) (AlgHom.id R S) x) i =
      Algebra.TensorProduct.map (f i) (AlgHom.id R S)
        (finiteProductBaseChangeEquiv R S B x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul b s =>
      simp only [Algebra.TensorProduct.map_tmul, finiteProductBaseChangeEquiv_tmul,
        AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, AlgHom.id_apply]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end SerrePositivity
