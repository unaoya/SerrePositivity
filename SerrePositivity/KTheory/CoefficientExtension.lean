module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Coefficient extension of additive maps and pairings

These constructions work for arbitrary abelian groups. They are shared by supported
G₀ and K₀, independently of localization, perfect complexes, or Adams operations.
The existing `g0CoefficientMap` name is retained for compatibility.
-/

@[expose] public section
noncomputable section
universe v
namespace SerrePositivity
open TensorProduct
variable (E : Type v) [CommRing E]

/-- Extend an additive group map to an E-linear map after tensoring over the integers. -/
def g0CoefficientMap {A C : Type*} [AddCommGroup A] [AddCommGroup C] (f : A →+ C) :
    E ⊗[ℤ] A →ₗ[E] E ⊗[ℤ] C := f.toIntLinearMap.baseChange E

@[simp] lemma g0CoefficientMap_tmul {A C : Type*} [AddCommGroup A] [AddCommGroup C]
    (f : A →+ C) (a : E) (x : A) : g0CoefficientMap E f (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] f x := rfl

lemma g0CoefficientMap_comp {A C D : Type*} [AddCommGroup A] [AddCommGroup C] [AddCommGroup D]
    (f : A →+ C) (g : C →+ D) :
    (g0CoefficientMap E g).comp (g0CoefficientMap E f) = g0CoefficientMap E (g.comp f) := by
  ext a
  rfl

@[simp]
lemma g0CoefficientMap_id {A : Type*} [AddCommGroup A] :
    g0CoefficientMap E (AddMonoidHom.id A) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro a x
  rfl

/-- A commuting square of additive maps remains commuting after extending coefficients. -/
lemma g0CoefficientMap_naturality {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    (f : A →+ B) (g : C →+ D) (i : A →+ C) (j : B →+ D)
    (h : ∀ x, j (f x) = g (i x)) (x : E ⊗[ℤ] A) :
    g0CoefficientMap E j (g0CoefficientMap E f x) =
      g0CoefficientMap E g (g0CoefficientMap E i x) := by
  have he : j.comp f = g.comp i := AddMonoidHom.ext h
  have hc := congrArg (fun k => g0CoefficientMap E k) he
  rw [← g0CoefficientMap_comp, ← g0CoefficientMap_comp] at hc
  exact DFunLike.congr_fun hc x

/-- Regard a biadditive pairing as a bilinear map over the integers. -/
def integerPairing {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B →+ C) : A →ₗ[ℤ] B →ₗ[ℤ] C where
  toFun x := (f x).toIntLinearMap
  map_add' x y := by ext z; exact congrArg (fun g : B →+ C => g z) (f.map_add x y)
  map_smul' n x := by ext z; exact congrArg (fun g : B →+ C => g z) (f.map_zsmul n x)

/-- Extend both arguments of an integer pairing to an E-bilinear pairing. -/
def coefficientPairing {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B →+ C) : E ⊗[ℤ] A →ₗ[E] E ⊗[ℤ] B →ₗ[E] E ⊗[ℤ] C :=
  TensorProduct.curry
    ((TensorProduct.lift (integerPairing f)).baseChange E ∘ₗ
      (AlgebraTensorModule.distribBaseChange ℤ E A B).symm.toLinearMap)

@[simp]
lemma coefficientPairing_tmul {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B →+ C) (a b : E) (x : A) (y : B) :
    coefficientPairing E f (a ⊗ₜ[ℤ] x) (b ⊗ₜ[ℤ] y) = (a * b) ⊗ₜ[ℤ] f x y := by
  simp only [coefficientPairing, TensorProduct.curry_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AlgebraTensorModule.distribBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, TensorProduct.lift.tmul]
  rfl

/-- A compatible triple of additive maps preserves the extended bilinear pairings. -/
lemma coefficientPairing_naturality {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (f : A →+ B →+ C) (g : A' →+ B' →+ C')
    (α : A →+ A') (β : B →+ B') (γ : C →+ C')
    (h : ∀ x y, γ (f x y) = g (α x) (β y)) (x : E ⊗[ℤ] A) (y : E ⊗[ℤ] B) :
    g0CoefficientMap E γ (coefficientPairing E f x y) =
      coefficientPairing E g (g0CoefficientMap E α x) (g0CoefficientMap E β y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y => simp only [coefficientPairing_tmul, g0CoefficientMap_tmul, h]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

end SerrePositivity
