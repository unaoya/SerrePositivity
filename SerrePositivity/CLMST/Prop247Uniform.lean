module

public import SerrePositivity.CLMST.IsogenyDescent
public import SerrePositivity.HomologicalAlgebra.ConeOfSurjectiveSource

/-! # Prop 2.4.7：固定した比較錐からの全段共通指数

実中間対象 P → E ← F を許す。almost 比較の存在は引数であり、
almost 圏の逆射を通常の逆射として選ばない。
Claim 2.4.8 の指数を剰余を取る前に選び、その後で全段へ移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {B L P E : Type u} [CommRing B] [IsReduced B]
    [AddCommGroup L] [Module B L] [Module.Finite B L]
    [AddCommGroup P] [Module B P] [AddCommGroup E] [Module B E]

/-- 固定した有限自由比較を、中間対象を通る実比較へ移す。
必要な almost 条件は、二つの核と有限自由側の余核の g による零化。
原典の有限自由比較が与えられた段階の条件付き定理である。 -/
theorem prop247_fixed_cone_of_common_comparison
    (g : B) (r : ℕ) (β : L →ₗ[B] P) (u : L →ₗ[B] (Fin r → B))
    (v : P →ₗ[B] E) (w : (Fin r → B) →ₗ[B] E)
    (hsq : v.comp β = w.comp u)
    (hu : Function.Bijective (awayModuleMap g u))
    (hv : ∀ y : P, v y = 0 → g • y = 0)
    (hw : ∀ z : (Fin r → B), w z = 0 → g • z = 0)
    (hcw : ∀ y : E ⧸ w.range, g • y = 0) :
    ∃ q : ℕ, moduleMapConeScalar B β (g ^ q) = 0 := by
  obtain ⟨q, _, hk, hc⟩ := finiteFreeConeIsogeny_with_annihilators B g r u hu
  have hk' (x : L) (hx : u x = 0) : g ^ q • x = 0 :=
    congrArg Subtype.val (hk ⟨x, hx⟩)
  have hs (x : L) : v (β x) = w (u x) := LinearMap.congr_fun hsq x
  refine ⟨(q + 1) + (q + 2), ?_⟩
  rw [pow_add]
  apply moduleMapConeScalar_eq_zero_of_ker_coker_annihilated B β
  · intro x hx
    have hz : u (g • x) = 0 := by
      rw [map_smul]
      apply hw
      rw [← hs, hx, map_zero]
    simpa only [pow_succ, mul_smul] using hk' (g • x) hz
  · intro y
    obtain ⟨y, rfl⟩ := β.range.mkQ_surjective y
    have hm : g • v y ∈ w.range := by
      apply (Submodule.Quotient.mk_eq_zero w.range).mp
      exact (map_smul w.range.mkQ g (v y)).trans (hcw _)
    obtain ⟨z, hz⟩ := hm
    have hm' : g ^ q • z ∈ u.range := by
      apply (Submodule.Quotient.mk_eq_zero u.range).mp
      exact (map_smul u.range.mkQ (g ^ q) z).trans (hc _)
    obtain ⟨x, hx⟩ := hm'
    have he : v (g ^ (q + 1) • y - β x) = 0 := by
      rw [map_sub, map_smul, hs, hx, map_smul, hz, ← mul_smul, ← pow_succ, sub_self]
    have he' : g ^ (q + 2) • y = β (g • x) := by
      have hh := hv _ he
      rw [smul_sub, ← mul_smul, ← pow_succ', ← map_smul] at hh
      exact sub_eq_zero.mp hh
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero β.range).mpr
    exact ⟨g • x, he'.symm⟩

omit [IsReduced B] [Module.Finite B L] in
/-- 一つの実錐の零射は、全ての p 冪剰余・全次数に同じ指数を与える。
指数は n より前に選ぶ。有限自由錐との同型は要求しない。 -/
theorem prop247_uniform_reductions_of_fixed_cone
    {R : Type u} [CommRing R] (φ : R →+* B) (a g : R)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (β : L →ₗ[B] P)
    (hβ : ∃ q : ℕ, moduleMapConeScalar B β ((φ g) ^ q) = 0)
    (comparison : ∀ n : ℕ,
      ((boundedAboveDerivedBaseChange φ).obj
        ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj ≅
      (derivedScalarConeFunctor B ((φ a) ^ n)).obj (moduleMapCone B β)) :
    ∃ q : ℕ, ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat B) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj,
        (φ g) ^ q • x = 0 := by
  obtain ⟨q, hq⟩ := hβ
  refine ⟨q, fun n i _ x => ?_⟩
  let e := (DerivedCategory.homologyFunctor (ModuleCat B) i).mapIso (comparison n)
  apply e.toLinearEquiv.injective
  simp only [map_smul, map_zero]
  exact derivedScalarCone_homology_annihilated_of_scalar_eq_zero B
    ((φ a) ^ n) (moduleMapCone B β) ((φ g) ^ q) hq i (e.hom x)

/-- 中間対象の almost 比較、始域の全射な完備化、剰余比較を順に合成する。
全段共通指数を結論として供給し、各段の指数を入力にはしない。 -/
theorem prop247_uniform_of_common_comparison
    {R Q : Type u} [CommRing R] [AddCommGroup Q] [Module B Q]
    (φ : R →+* B) (a g : R)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (r : ℕ) (β : L →ₗ[B] P) (u : L →ₗ[B] (Fin r → B))
    (v : P →ₗ[B] E) (w : (Fin r → B) →ₗ[B] E)
    (hsq : v.comp β = w.comp u)
    (hu : Function.Bijective (awayModuleMap (φ g) u))
    (hv : ∀ y : P, v y = 0 → φ g • y = 0)
    (hw : ∀ z : (Fin r → B), w z = 0 → φ g • z = 0)
    (hcw : ∀ y : E ⧸ w.range, φ g • y = 0)
    (t : L →ₗ[B] Q) (ht : Function.Surjective t)
    (α : Q →ₗ[B] P) (hα : α.comp t = β)
    (comparison : ∀ n : ℕ,
      ((boundedAboveDerivedBaseChange φ).obj
        ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj ≅
      (derivedScalarConeFunctor B ((φ a) ^ n)).obj (moduleMapCone B α)) :
    ∃ q : ℕ, ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat B) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj,
        (φ g) ^ q • x = 0 := by
  obtain ⟨q, hq⟩ := prop247_fixed_cone_of_common_comparison (φ g) r β u v w hsq hu hv hw hcw
  exact prop247_uniform_reductions_of_fixed_cone φ a g f α
    ⟨2 * q, moduleMapConeScalar_of_surjective_source t ht α β hα (φ g) q hq⟩ comparison

end SerrePositivity.CLMST
