module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.LocalRing.Pullback

/-! # Kernel and cokernel annihilators from an actual pullback square

The pullback is the categorical one, rather than a new excision assumption.
No finiteness, flatness, completeness or surjectivity of a square edge is used.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits

/-- The concrete fiber-product algebra is the categorical ring pullback. -/
theorem algHom_isPullback_pullback
    {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D]
    (r : B →ₐ[R] D) (b : C →ₐ[R] D) :
    IsPullback (CommRingCat.ofHom (AlgHom.pullbackFst r b).toRingHom)
      (CommRingCat.ofHom (AlgHom.pullbackSnd r b).toRingHom)
      (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom) := by
  letI : ReflectsLimit
      (cospan (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom))
      (forget CommRingCat) := reflectsLimit_of_reflectsIsomorphisms _ _
  have hcomm : CommRingCat.ofHom (AlgHom.pullbackFst r b).toRingHom ≫
      CommRingCat.ofHom r.toRingHom =
      CommRingCat.ofHom (AlgHom.pullbackSnd r b).toRingHom ≫ CommRingCat.ofHom b.toRingHom := by
    ext x
    exact x.property
  apply (IsPullback.map_iff (forget CommRingCat) hcomm).mp
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact x.property
  · intro x y h
    exact Subtype.ext (Prod.ext h.1 h.2)
  · intro x y h
    exact ⟨⟨(x, y), h⟩, rfl, rfl⟩

/-- A scalar killing both bottom objects of a pullback square kills the kernel
and cokernel of its top horizontal linear map. -/
theorem linearMap_ker_coker_annihilated_of_type_isPullback
    {R M N P Q : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] N) (l : M →ₗ[R] P) (r : N →ₗ[R] Q) (b : P →ₗ[R] Q)
    (hPB : IsPullback (↾f : M ⟶ N) (↾l : M ⟶ P) (↾r : N ⟶ Q) (↾b : P ⟶ Q))
    (a : R) (hP : ∀ x : P, a • x = 0) (hQ : ∀ y : Q, a • y = 0) :
    (∀ x : f.ker, a • x = 0) ∧ (∀ y : N ⧸ f.range, a • y = 0) := by
  constructor
  · intro x
    apply Subtype.ext
    change a • (x : M) = 0
    apply Types.ext_of_isPullback hPB
    · change f (a • (x : M)) = f 0
      rw [map_smul, x.property, smul_zero, map_zero]
    · change l (a • (x : M)) = l 0
      rw [map_smul, map_zero]
      exact hP _
  · intro y
    refine Submodule.Quotient.induction_on _ y ?_
    intro z
    have hz : r (a • z) = b 0 := by
      rw [map_smul, map_zero]
      exact hQ _
    obtain ⟨x, hx, _⟩ := Types.exists_of_isPullback hPB (a • z) 0 hz
    exact (Submodule.Quotient.mk_eq_zero f.range).mpr ⟨x, hx⟩

/-- A scalar vanishing in the bottom-left algebra of an actual ring pullback
annihilates the kernel and cokernel over the original scalar ring. -/
theorem algHom_ker_coker_annihilated_of_isPullback
    {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] B) (l : A →ₐ[R] C) (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hPB : IsPullback (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom l.toRingHom)
      (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (a : R) (ha : algebraMap R C a = 0) :
    (∀ x : f.toLinearMap.ker, a • x = 0) ∧
      (∀ y : B ⧸ f.toLinearMap.range, a • y = 0) := by
  have hPB' : IsPullback (↾f : A ⟶ B) (↾l : A ⟶ C) (↾r : B ⟶ D) (↾b : C ⟶ D) :=
    hPB.map (forget CommRingCat)
  have hb : algebraMap R D a = 0 := by
    rw [← b.commutes, ha, map_zero]
  apply linearMap_ker_coker_annihilated_of_type_isPullback
    f.toLinearMap l.toLinearMap r.toLinearMap b.toLinearMap hPB' a
  · intro x
    rw [Algebra.smul_def, ha, zero_mul]
  · intro y
    rw [Algebra.smul_def, hb, zero_mul]

end SerrePositivity
