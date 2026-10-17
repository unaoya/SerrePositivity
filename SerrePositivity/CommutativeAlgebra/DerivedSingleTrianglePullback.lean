module

public import SerrePositivity.HomologicalAlgebra.SingleTriangleExactReflection
public import SerrePositivity.CommutativeAlgebra.PullbackAnnihilator
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Ordinary ring pullbacks from actual distinguished single-module triangles

The middle module is the product and the second map is the difference of the
two original maps. The connecting map and distinguishedness must be supplied.
This does not construct any derived perfectoidization or invoke excision.
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {R : Type v} {A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

/-- The short complex of the original square: a ↦ (f a,l a),
followed by (x,y) ↦ r x-b y. -/
def algHomPullbackShortComplex
    (f : A →ₐ[R] B) (l : A →ₐ[R] C) (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hcomm : r.comp f = b.comp l) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (f.toLinearMap.prod l.toLinearMap))
    (ModuleCat.ofHom (r.toLinearMap.comp (LinearMap.fst R B C) -
      b.toLinearMap.comp (LinearMap.snd R B C))) (by
        ext a
        change r (f a) - b (l a) = 0
        exact sub_eq_zero.mpr (AlgHom.congr_fun hcomm a))

/-- Short exactness of the original product/difference complex implies the
categorical ring pullback. No ring edge is assumed surjective. -/
theorem algHom_isPullback_of_module_shortExact
    (f : A →ₐ[R] B) (l : A →ₐ[R] C) (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hcomm : r.comp f = b.comp l)
    (hS : (algHomPullbackShortComplex f l r b hcomm).ShortExact) :
    IsPullback (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom l.toRingHom)
      (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom) := by
  let S := algHomPullbackShortComplex f l r b hcomm
  have hinj : Function.Injective S.f := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hex := (ShortComplex.moduleCat_exact_iff S).mp hS.exact
  let : ReflectsLimit (cospan (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom))
      (forget CommRingCat) := reflectsLimit_of_reflectsIsomorphisms _ _
  apply IsPullback.of_map_of_faithful (forget CommRingCat)
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext a
    exact AlgHom.congr_fun hcomm a
  · intro x y hxy
    apply hinj
    exact Prod.ext hxy.1 hxy.2
  · intro x y hxy
    have hz : S.g (x, y) = 0 := sub_eq_zero.mpr hxy
    obtain ⟨a, ha⟩ := hex (x, y) hz
    exact ⟨a, congrArg Prod.fst ha, congrArg Prod.snd ha⟩

/-- An actual distinguished triangle with the specified discrete modules and
product/difference maps gives the original categorical ring pullback. -/
theorem algHom_isPullback_of_distinguished_single_triangle
    (f : A →ₐ[R] B) (l : A →ₐ[R] C) (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hcomm : r.comp f = b.comp l)
    (δ : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R D) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R A))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (algHomPullbackShortComplex f l r b hcomm).f)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (algHomPullbackShortComplex f l r b hcomm).g) δ ∈ distTriang _) :
    IsPullback (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom l.toRingHom)
      (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom) :=
  algHom_isPullback_of_module_shortExact f l r b hcomm
    (shortExact_of_distinguished_single_triangle (algHomPullbackShortComplex f l r b hcomm) δ hT)

/-- The product/difference complex of arbitrary ring homomorphisms, using
only their canonical integer-module structures. -/
def ringHomPullbackShortComplex
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (l : A →+* C) (r : B →+* D) (b : C →+* D)
    (hcomm : r.comp f = b.comp l) : ShortComplex (ModuleCat.{u} ℤ) :=
  algHomPullbackShortComplex f.toIntAlgHom l.toIntAlgHom r.toIntAlgHom b.toIntAlgHom
    (AlgHom.ext (fun x => RingHom.congr_fun hcomm x))

/-- The actual integer-module distinguished triangle gives the categorical
ring pullback, without choosing any extra coefficient-algebra structures. -/
theorem ringHom_isPullback_of_distinguished_single_triangle
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (l : A →+* C) (r : B →+* D) (b : C →+* D)
    (hcomm : r.comp f = b.comp l)
    (δ : (DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).obj (ModuleCat.of ℤ D) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).obj (ModuleCat.of ℤ A))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      ((DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).map
        (ringHomPullbackShortComplex f l r b hcomm).f)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).map
        (ringHomPullbackShortComplex f l r b hcomm).g) δ ∈ distTriang _) :
    IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom l)
      (CommRingCat.ofHom r) (CommRingCat.ofHom b) :=
  algHom_isPullback_of_distinguished_single_triangle
    f.toIntAlgHom l.toIntAlgHom r.toIntAlgHom b.toIntAlgHom
    (AlgHom.ext (fun x => RingHom.congr_fun hcomm x)) δ hT

end SerrePositivity
