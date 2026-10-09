module

public import SerrePositivity.Statement
public import SerrePositivity.HomologicalAlgebra.ResolutionOfCochain
public import SerrePositivity.PerfectComplex.Basic
public import Mathlib.RingTheory.KrullDimension.Module

/-!
# Standard intersection-theory inputs

These Prop-valued interfaces record general results missing from the current
library: finite free resolutions over regular local rings, ordinary Tor and
its finiteness, additivity, and generic-basis dimension facts. Vanishing is the
Roberts--Gillet--Soulé theorem. No field mentions normalized lengths, group
actions, norm comparisons, or the conclusion of Lemma 5.2.

No instances or axioms are installed here. The theorem using these inputs is
conditional until these interfaces are supplied by proofs or named external inputs.
-/

public section

universe u

open CategoryTheory TensorProduct

namespace SerrePositivity.Inputs

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- Standard homological algebra over a regular local ring (layer 3a). -/
class RegularHomologicalAlgebra : Prop where
  /-- Finite modules admit bounded resolutions by finite free modules. -/
  resolution : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    ∃ F : CochainComplex (ModuleCat.{u} R) ℤ,
      Nonempty (IsResolutionOf F (ModuleCat.of R M)) ∧
      (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → CategoryTheory.Limits.IsZero (F.X i)) ∧
      (∀ i, Module.Free R (F.X i)) ∧ (∀ i, Module.Finite R (F.X i))
  /-- Forgetting the coefficient action identifies extension-of-scalars Tor
  with the ordinary `R`-module Tor, computed using the same resolution. -/
  ordinaryTorIso : ∀ (T : Type u) [CommRing T] [Algebra R T]
      (M : Type u) [AddCommGroup M] [Module R M]
      (F : CochainComplex (ModuleCat.{u} R) ℤ),
    IsResolutionOf F (ModuleCat.of R M) → ∀ i : ℕ,
      Nonempty (((ModuleCat.restrictScalars (algebraMap R T)).obj
        ((baseChange (algebraMap R T) F).homology (-(i : ℤ)))) ≃ₗ[R] TorModule R i T M)
  /-- Tor has finite length when a finite pair has finite-length tensor product. -/
  finiteTor : ∀ (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N], Module.length R (M ⊗[R] N) ≠ ⊤ →
      ∀ i : ℕ, Module.length R (TorModule R i M N) ≠ ⊤

/-- Additivity and finite-direct-sum evaluation of the intersection characteristic (layer 3a). -/
class IntersectionAdditivity : Prop where
  add_left : ∀ (M₁ M₂ M₃ N : Type u) [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N] [Module R N] [Module.Finite R M₁] [Module.Finite R M₂]
    [Module.Finite R M₃] [Module.Finite R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
    Module.length R (M₂ ⊗[R] N) ≠ ⊤ → chi R M₂ N = chi R M₁ N + chi R M₃ N
  add_right : ∀ (M N₁ N₂ N₃ : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃] [Module.Finite R M] [Module.Finite R N₁]
    [Module.Finite R N₂] [Module.Finite R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
    Module.length R (M ⊗[R] N₂) ≠ ⊤ → chi R M N₂ = chi R M N₁ + chi R M N₃
  pi_left : ∀ (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N], Module.length R (M ⊗[R] N) ≠ ⊤ →
    ∀ n : ℕ, chi R (Fin n → M) N = (n : ℤ) * chi R M N
  pi_right : ∀ (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N], Module.length R (M ⊗[R] N) ≠ ⊤ →
    ∀ n : ℕ, chi R M (Fin n → N) = (n : ℤ) * chi R M N

/-- General finite-module support and generic-rank facts (layer 3a). -/
class FiniteModuleGeometry : Prop where
  /-- Finite modules with annihilator intersection at the closed point have
  finite-length tensor product. -/
  tensor_finite : ∀ (I J : Ideal R)
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N],
    I ≤ Module.annihilator R M → J ≤ Module.annihilator R N →
    (I ⊔ J).radical = IsLocalRing.maximalIdeal R → Module.length R (M ⊗[R] N) ≠ ⊤
  /-- A generic basis gives an injection with a lower-dimensional cokernel. -/
  generic_basis : ∀ (I : Ideal R) [I.IsPrime]
    (M : Type u) [AddCommGroup M] [Module R M] [Module (R ⧸ I) M]
    [IsScalarTower R (R ⧸ I) M] [Module.Finite R M] [Module.Finite (R ⧸ I) M],
    0 < Module.finrank (R ⧸ I) M →
    ∃ f : (Fin (Module.finrank (R ⧸ I) M) → R ⧸ I) →ₗ[R] M,
      Function.Injective f ∧
        Module.supportDim R (M ⧸ LinearMap.range f) < ringKrullDim (R ⧸ I)
  /-- Positive generic rank makes a finite module have the full support dimension. -/
  supportDim_of_rank_pos : ∀ (I : Ideal R) [I.IsPrime]
    (M : Type u) [AddCommGroup M] [Module R M] [Module (R ⧸ I) M]
    [IsScalarTower R (R ⧸ I) M] [Module.Finite R M] [Module.Finite (R ⧸ I) M],
    0 < Module.finrank (R ⧸ I) M → Module.supportDim R M = ringKrullDim (R ⧸ I)
  /-- Integral finite domain extensions of positive rank preserve ring dimension. -/
  ringDim_of_rank_pos : ∀ (I : Ideal R) [I.IsPrime]
    (T : Type u) [CommRing T] [IsDomain T] [Algebra (R ⧸ I) T] [Module.Finite (R ⧸ I) T],
    0 < Module.finrank (R ⧸ I) T → ringKrullDim T = ringKrullDim (R ⧸ I)

/-- Roberts--Gillet--Soulé vanishing (paper (5.1), layer 3b). -/
class IntersectionVanishing : Prop where
  vanish : ∀ (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N], Module.length R (M ⊗[R] N) ≠ ⊤ →
    Module.supportDim R M + Module.supportDim R N < ringKrullDim R → chi R M N = 0

end SerrePositivity.Inputs
