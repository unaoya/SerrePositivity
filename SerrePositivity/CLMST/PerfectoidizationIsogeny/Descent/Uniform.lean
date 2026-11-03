module

public import SerrePositivity.HomologicalAlgebra.CompleteFaithfullyFlatDescent
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Descent.StandardSquare
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion

/-! # 固定した比較錐からの全段の共通指数と降下

## 概要

実際の中間対象 `P → E ← F` を通る比較の錐が固定されているとき、Claim 2.4.8 の指数を剰余を取る前に選び、全ての剰余段に共通の指数を得る（`uniform_reductions_of_fixed_cone` ほか）。基底変更先の有限被覆の元から元の写像の錐へ降下し（`isogeny_of_standard_finite_cover`）、指定した perfectoid 化の標準比較について全段の共通指数と降下を与える。

## 方針

almost 比較の存在は引数として受け取り、almost 圏の逆射を通常の逆射として選ばない。降下は HomologicalAlgebra/CompleteFaithfullyFlatDescent の D1〜D6 による。

## 規約

CLMST（arXiv:2209.04046v4）Prop 2.4.7 の証明の降下の段。被覆の元は基底変更先に属してよく、大域的な有限自由比較は仮定しない。旧 `CLMST/Prop247Uniform`・`Prop247CoveredDescent`・`Prop247UniformStandard`。

## 使われ方

`GeneralRank`・`Proof`。
-/

@[expose] public noncomputable section

universe u

section Prop247UniformPart

namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {B L P E : Type u} [CommRing B] [IsReduced B]
    [AddCommGroup L] [Module B L] [Module.Finite B L]
    [AddCommGroup P] [Module B P] [AddCommGroup E] [Module B E]

/-- 分母の冪を伴う有限自由比較を、中間対象を通る実比較へ移す。
必要な almost 条件は、二つの核と有限自由側の余核の g による零化。
分母を払う冪 k は錐を零化する指数の一様性を損なわない。 -/
theorem fixed_cone_of_scaled_common_comparison
    (g : B) (r : ℕ) (β : L →ₗ[B] P) (u : L →ₗ[B] (Fin r → B))
    (v : P →ₗ[B] E) (w : (Fin r → B) →ₗ[B] E)
    (k : ℕ) (hsq : (g ^ k • v).comp β = w.comp u)
    (hu : Function.Bijective (awayModuleMap g u))
    (hv : ∀ y : P, v y = 0 → g • y = 0)
    (hw : ∀ z : (Fin r → B), w z = 0 → g • z = 0)
    (hcw : ∀ y : E ⧸ w.range, g • y = 0) :
    ∃ q : ℕ, moduleMapConeScalar B β (g ^ q) = 0 := by
  obtain ⟨q, _, hk, hc⟩ := finiteFreeConeIsogeny_with_annihilators B g r u hu
  have hk' (x : L) (hx : u x = 0) : g ^ q • x = 0 :=
    congrArg Subtype.val (hk ⟨x, hx⟩)
  have hs (x : L) : g ^ k • v (β x) = w (u x) := LinearMap.congr_fun hsq x
  refine ⟨(q + 1) + (q + 2), ?_⟩
  rw [pow_add]
  apply moduleMapConeScalar_eq_zero_of_ker_coker_annihilated B β
  · intro x hx
    have hz : u (g • x) = 0 := by
      rw [map_smul]
      apply hw
      rw [← hs, hx, map_zero, smul_zero]
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
    have he : v (g ^ (q + 1) • y - β (g ^ k • x)) = 0 := by
      rw [map_sub, map_smul, map_smul, map_smul, hs, hx, map_smul, hz,
        ← mul_smul, ← pow_succ, sub_self]
    have he' : g ^ (q + 2) • y = β (g • (g ^ k • x)) := by
      have hh := hv _ he
      rw [smul_sub, ← mul_smul, ← pow_succ', ← map_smul] at hh
      exact sub_eq_zero.mp hh
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero β.range).mpr
    exact ⟨g • (g ^ k • x), he'.symm⟩

/-- 固定した有限自由比較を、中間対象を通る実比較へ移す。
元の可換図式の場合は分母の冪を 0 として前の定理を使う。 -/
theorem fixed_cone_of_common_comparison
    (g : B) (r : ℕ) (β : L →ₗ[B] P) (u : L →ₗ[B] (Fin r → B))
    (v : P →ₗ[B] E) (w : (Fin r → B) →ₗ[B] E)
    (hsq : v.comp β = w.comp u)
    (hu : Function.Bijective (awayModuleMap g u))
    (hv : ∀ y : P, v y = 0 → g • y = 0)
    (hw : ∀ z : (Fin r → B), w z = 0 → g • z = 0)
    (hcw : ∀ y : E ⧸ w.range, g • y = 0) :
    ∃ q : ℕ, moduleMapConeScalar B β (g ^ q) = 0 := by
  exact fixed_cone_of_scaled_common_comparison g r β u v w 0
    (by simpa only [pow_zero, one_smul] using hsq) hu hv hw hcw

omit [IsReduced B] [Module.Finite B L] in
/-- 一つの実錐の零射は、全ての p 冪剰余・全次数に同じ指数を与える。
指数は n より前に選ぶ。有限自由錐との同型は要求しない。 -/
theorem uniform_reductions_of_fixed_cone
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
theorem uniform_of_common_comparison
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
  obtain ⟨q, hq⟩ := fixed_cone_of_common_comparison (φ g) r β u v w hsq hu hv hw hcw
  exact uniform_reductions_of_fixed_cone φ a g f α
    ⟨2 * q, moduleMapConeScalar_of_surjective_source t ht α β hα (φ g) q hq⟩ comparison

end SerrePositivity.CLMST

end Prop247UniformPart

section Prop247UniformStandardPart

namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S B C P E : Type u) [CommRing R] [CommRing S] [CommRing B]
    [CommRing C] [CommRing P] [Algebra R S] [Algebra R B] [Algebra R C] [Algebra B P]
    [AddCommGroup E] [Module B E]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hB : IsIntegralPerfectoid B p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (r : ℕ) (β : B ⊗[R] S →ₐ[B] P)
    (hβ : IsPerfectoidization p β.toRingHom)
    (u : (B ⊗[R] S) →ₗ[B] (Fin r → B))
    (v : P →ₗ[B] E) (w : (Fin r → B) →ₗ[B] E)
    (hsq : v.comp β.toLinearMap = w.comp u)
    (hu : Function.Bijective (awayModuleMap (algebraMap R B g) u))
    (hv : ∀ y : P, v y = 0 → algebraMap R B g • y = 0)
    (hw : ∀ z : (Fin r → B), w z = 0 → algebraMap R B g • z = 0)
    (hcw : ∀ y : E ⧸ w.range, algebraMap R B g • y = 0)

include hR hB hf hbounded hβ hsq hu hv hw hcw

/-- 元の実比較から、全剰余段に共通の一つの指数を得る。
指数の存在は段 n より先であり、段ごとの指数を仮定しない。 -/
theorem uniform_of_standard_comparison
    (hflat : IsCompletelyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B))) :
    ∃ q : ℕ, ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat B) i).obj
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          ((boundedAboveDerivedScalarCone R ((p : R) ^ n)).obj
            (moduleMapConeBoundedAbove f.toLinearMap))).obj,
        (algebraMap R B g) ^ q • x = 0 := by
  obtain ⟨N, hN⟩ := hbounded
  let := hB.isReduced B p
  let := Module.FinitePresentation.of_finite_of_finitePresentation R S
  let α := (completionMap p β hβ).toLinearMap
  let t := (IsScalarTower.toAlgHom B (B ⊗[R] S)
    (AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S))).toLinearMap
  have hα : α.comp t = β.toLinearMap := by
    ext x
    exact completionMap_unit p β hβ x
  apply uniform_of_common_comparison (algebraMap R B) (p : R) g f.toLinearMap
    r β.toLinearMap u v w hsq hu hv hw hcw t
    (tensor_completion_unit_surjective B p R S hB) α hα
  intro n
  simpa only [map_natCast] using standardReductionConeIso R S B C P p hR hB
    f hf β hβ hflat N hN n

/-- 指定した元の実 perfectoid 化写像の錐・核・余核へ共通指数を忠実降下する。 -/
theorem isogeny_of_standard_comparison
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B))) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
      (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ x : C ⧸ f.toLinearMap.range, g ^ q • x = 0) := by
  exact moduleMapConeIsogeny_descent (algebraMap R B) (p : R) hflat f.toLinearMap
    (cone_isComplete_of_perfectoid_target R S p hR C hf.1 f.toLinearMap) g
    (uniform_of_standard_comparison R S B C P E p hR hB f hf hbounded g r β hβ
      u v w hsq hu hv hw hcw hflat.1)

end SerrePositivity.CLMST

end Prop247UniformStandardPart

section Prop247CoveredDescentPart

namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R S B C P : Type u) [CommRing R] [CommRing S] [CommRing B]
    [CommRing C] [CommRing P] [Algebra R S] [Algebra R B] [Algebra R C] [Algebra B P]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hB : IsIntegralPerfectoid B p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (β : B ⊗[R] S →ₐ[B] P) (hβ : IsPerfectoidization p β.toRingHom)

include hR hB hf hbounded hβ

/-- 一つの実 β 錐の冪零化から、元の f の全剰余段へ共通指数を移す。
始域・終域・実錐・剰余段の比較は既存の標準構成から供給する。 -/
theorem uniform_of_standard_fixed_cone
    (hflat : IsCompletelyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B)))
    (hfixed : ∃ q : ℕ,
      moduleMapConeScalar B β.toLinearMap ((algebraMap R B g) ^ q) = 0) :
    ∃ q : ℕ, ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat B) i).obj
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          ((boundedAboveDerivedScalarCone R ((p : R) ^ n)).obj
            (moduleMapConeBoundedAbove f.toLinearMap))).obj,
        (algebraMap R B g) ^ q • x = 0 := by
  obtain ⟨N, hN⟩ := hbounded
  obtain ⟨q, hq⟩ := hfixed
  let := Module.FinitePresentation.of_finite_of_finitePresentation R S
  let α := (completionMap p β hβ).toLinearMap
  let t := (IsScalarTower.toAlgHom B (B ⊗[R] S)
    (AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S))).toLinearMap
  have hα : α.comp t = β.toLinearMap := by
    ext x
    exact completionMap_unit p β hβ x
  apply uniform_reductions_of_fixed_cone (algebraMap R B) (p : R) g f.toLinearMap α
    ⟨2 * q, moduleMapConeScalar_of_surjective_source t
      (tensor_completion_unit_surjective B p R S hB) α β.toLinearMap hα
      (algebraMap R B g) q hq⟩
  intro n
  simpa only [map_natCast] using standardReductionConeIso R S B C P p hR hB
    f hf β hβ hflat N hN n

/-- 実有限被覆上の β の錐零化を合流し、全段共通指数を介して元の f へ降下する。
各被覆部分に同じ rank や同じ局所指数を要求しない。 -/
theorem isogeny_of_standard_finite_cover
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B)))
    (t : Finset B)
    (hcover : ∃ k : ℕ, (algebraMap R B g) ^ k ∈ Ideal.span (t : Set B))
    (hlocal : ∀ d ∈ t, ∃ q : ℕ, moduleMapConeScalar B β.toLinearMap (d ^ q) = 0) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
      (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ x : C ⧸ f.toLinearMap.range, g ^ q • x = 0) := by
  have hfixed := moduleMapConeScalar_of_finite_cover β.toLinearMap
    (algebraMap R B g) t hcover hlocal
  exact moduleMapConeIsogeny_descent (algebraMap R B) (p : R) hflat f.toLinearMap
    (cone_isComplete_of_perfectoid_target R S p hR C hf.1 f.toLinearMap) g
    (uniform_of_standard_fixed_cone R S B C P p hR hB f hf hbounded g β hβ hflat.1 hfixed)

end SerrePositivity.CLMST

end Prop247CoveredDescentPart
