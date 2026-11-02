module

public import SerrePositivity.BhattScholze.Perfectoidization.FiniteComparisonExcision
public import SerrePositivity.CommutativeAlgebra.DerivedSingleTrianglePullback

/-! # The exact integer-module triangle needed for canonical perfectoid excision

Both units and all four ring homomorphisms are fixed. This supplies the ordinary
ring pullback once the actual distinguished triangle has been identified.
No derived perfectoidization model or excision input is asserted here.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated BhattScholze
attribute [local instance] HasDerivedCategory.standard
variable {R A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C} {g : B →ₐ[R] D}

/-- The integer-module product/difference complex of the original canonical
excision square, using precisely its original four ring homomorphisms. -/
def canonicalExcisionIntegerModuleComplex
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (q : A →ₐ[R] B) (a : R) : ShortComplex (ModuleCat.{u} ℤ) :=
  ringHomPullbackShortComplex (IsPerfectoidization.map hf hg q.toRingHom)
    (perfectoidizationClosedSideProjection hf (Ideal.span {algebraMap R A a}))
    (perfectoidizationClosedSideProjection hg
      ((Ideal.span {algebraMap R A a}).map q.toRingHom))
    (perfectoidizationClosedComparison hf hg q.toRingHom (Ideal.span {algebraMap R A a}))
    (perfectoidizationClosedComparison_square hf hg q.toRingHom
      (Ideal.span {algebraMap R A a})).symm

/-- The actual distinguished triangle on the specified integer-module single
objects supplies exactly the missing canonical ring pullback assertion. -/
theorem canonicalExcision_isPullback_of_distinguished_single_triangle
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (q : A →ₐ[R] B) (a : R)
    (δ : (DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).obj
        (canonicalExcisionIntegerModuleComplex hf hg q a).X₃ ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).obj
        (canonicalExcisionIntegerModuleComplex hf hg q a).X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      ((DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).map
        (canonicalExcisionIntegerModuleComplex hf hg q a).f)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).map
        (canonicalExcisionIntegerModuleComplex hf hg q a).g) δ ∈ distTriang _) :
    BhattScholze.KLCanonicalExcisionSquare hf hg q a :=
  ringHom_isPullback_of_distinguished_single_triangle
    (IsPerfectoidization.map hf hg q.toRingHom)
    (perfectoidizationClosedSideProjection hf (Ideal.span {algebraMap R A a}))
    (perfectoidizationClosedSideProjection hg
      ((Ideal.span {algebraMap R A a}).map q.toRingHom))
    (perfectoidizationClosedComparison hf hg q.toRingHom (Ideal.span {algebraMap R A a}))
    (perfectoidizationClosedComparison_square hf hg q.toRingHom
      (Ideal.span {algebraMap R A a})).symm δ hT

end SerrePositivity.CLMST
