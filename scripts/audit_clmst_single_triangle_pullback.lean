import SerrePositivity.CommutativeAlgebra.DerivedSingleTrianglePullback
import Mathlib.Data.ZMod.Basic
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.shortExact_of_distinguished_single_triangle
assert_no_sorry SerrePositivity.shortExact_iff_exists_distinguished_single_triangle
assert_no_sorry SerrePositivity.algHomPullbackShortComplex
assert_no_sorry SerrePositivity.algHom_isPullback_of_module_shortExact
assert_no_sorry SerrePositivity.algHom_isPullback_of_distinguished_single_triangle
#print axioms SerrePositivity.shortExact_of_distinguished_single_triangle
#print axioms SerrePositivity.shortExact_iff_exists_distinguished_single_triangle
#print axioms SerrePositivity.algHomPullbackShortComplex
#print axioms SerrePositivity.algHom_isPullback_of_module_shortExact
#print axioms SerrePositivity.algHom_isPullback_of_distinguished_single_triangle

noncomputable section
universe u
open SerrePositivity CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

-- An actual algebra fiber product supplies an honest distinguished triangle.
-- Reflection is applied to that same triangle and its original ring maps.
theorem audit_actual_fiber_product_single_triangle
    (R B C D : Type u) [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D]
    (r : B →ₐ[R] D) (b : C →ₐ[R] D) (hr : Function.Surjective r) :
    let S := algHomPullbackShortComplex (AlgHom.pullbackFst r b) (AlgHom.pullbackSnd r b)
      r b (by ext x; exact x.property)
    ∃ δ : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S.X₃ ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S.X₁)⟦(1 : ℤ)⟧,
      Triangle.mk ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map S.f)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map S.g) δ ∈ distTriang _ ∧
      IsPullback (CommRingCat.ofHom (AlgHom.pullbackFst r b).toRingHom)
        (CommRingCat.ofHom (AlgHom.pullbackSnd r b).toRingHom)
        (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom) := by
  let f := AlgHom.pullbackFst r b
  let l := AlgHom.pullbackSnd r b
  have hcomm : r.comp f = b.comp l := by ext x; exact x.property
  let S := algHomPullbackShortComplex f l r b hcomm
  change ∃ δ : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S.X₃ ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S.X₁)⟦(1 : ℤ)⟧,
      Triangle.mk ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map S.f)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map S.g) δ ∈ distTriang _ ∧ _
  have he : S.Exact := by
    apply (ShortComplex.moduleCat_exact_iff S).mpr
    rintro ⟨x, y⟩ hxy
    change r x - b y = 0 at hxy
    exact ⟨⟨(x, y), sub_eq_zero.mp hxy⟩, rfl⟩
  have hm : Mono S.f := by
    apply (ModuleCat.mono_iff_injective S.f).mpr
    intro x y hxy
    exact Subtype.ext hxy
  have hn : Epi S.g := by
    apply (ModuleCat.epi_iff_surjective S.g).mpr
    intro z
    obtain ⟨x, hx⟩ := hr z
    refine ⟨(x, 0), ?_⟩
    change r x - b 0 = z
    rw [map_zero, sub_zero, hx]
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' he hm hn
  exact ⟨hS.singleδ, hS.singleTriangle_distinguished,
    algHom_isPullback_of_distinguished_single_triangle f l r b hcomm
      hS.singleδ hS.singleTriangle_distinguished⟩

-- Specialize the actual triangle construction to the integer/mod-two example.
theorem audit_mod_two_fiber_product_triangle :
    let q : ℤ →ₐ[ℤ] ZMod 2 := Algebra.ofId ℤ (ZMod 2)
    let S := algHomPullbackShortComplex (AlgHom.pullbackFst q q) (AlgHom.pullbackSnd q q)
      q q (by ext x; exact x.property)
    ∃ δ : (DerivedCategory.singleFunctor (ModuleCat ℤ) 0).obj S.X₃ ⟶
      ((DerivedCategory.singleFunctor (ModuleCat ℤ) 0).obj S.X₁)⟦(1 : ℤ)⟧,
      Triangle.mk ((DerivedCategory.singleFunctor (ModuleCat ℤ) 0).map S.f)
        ((DerivedCategory.singleFunctor (ModuleCat ℤ) 0).map S.g) δ ∈ distTriang _ := by
  obtain ⟨δ, hT, _⟩ := audit_actual_fiber_product_single_triangle ℤ ℤ ℤ (ZMod 2)
    (Algebra.ofId ℤ (ZMod 2)) (Algebra.ofId ℤ (ZMod 2)) ZMod.intCast_surjective
  exact ⟨δ, hT⟩

-- The difference map in the integer/mod-two fiber-product example has no
-- linear section. A distinguished single triangle must allow this case.
theorem audit_mod_two_difference_not_split :
    let q : ℤ →ₐ[ℤ] ZMod 2 := Algebra.ofId ℤ (ZMod 2)
    let d := q.toLinearMap.comp (LinearMap.fst ℤ ℤ ℤ) -
      q.toLinearMap.comp (LinearMap.snd ℤ ℤ ℤ)
    ¬ ∃ s : ZMod 2 →ₗ[ℤ] (ℤ × ℤ), d.comp s = LinearMap.id := by
  let q : ℤ →ₐ[ℤ] ZMod 2 := Algebra.ofId ℤ (ZMod 2)
  let d := q.toLinearMap.comp (LinearMap.fst ℤ ℤ ℤ) -
    q.toLinearMap.comp (LinearMap.snd ℤ ℤ ℤ)
  change ¬ ∃ s : ZMod 2 →ₗ[ℤ] (ℤ × ℤ), d.comp s = LinearMap.id
  rintro ⟨s, hs⟩
  have htwo : (2 : ℤ) • (1 : ZMod 2) = 0 := by
    rw [Algebra.smul_def]
    change (2 : ZMod 2) * 1 = 0
    simpa only [mul_one] using (show (2 : ZMod 2) = 0 by decide)
  have hzero : (2 : ℤ) • s 1 = 0 := by rw [← s.map_smul, htwo, map_zero]
  have hval : s 1 = 0 := (smul_eq_zero.mp hzero).resolve_left (by norm_num)
  have h := LinearMap.congr_fun hs 1
  change q (s 1).1 - q (s 1).2 = (1 : ZMod 2) at h
  rw [hval] at h
  simp at h

assert_no_sorry audit_actual_fiber_product_single_triangle
assert_no_sorry audit_mod_two_difference_not_split
#print axioms audit_actual_fiber_product_single_triangle
#print axioms audit_mod_two_difference_not_split

assert_no_sorry audit_mod_two_fiber_product_triangle
#print axioms audit_mod_two_fiber_product_triangle

assert_no_sorry SerrePositivity.ringHomPullbackShortComplex
assert_no_sorry SerrePositivity.ringHom_isPullback_of_distinguished_single_triangle
#print axioms SerrePositivity.ringHomPullbackShortComplex
#print axioms SerrePositivity.ringHom_isPullback_of_distinguished_single_triangle
