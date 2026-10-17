module

public import SerrePositivity.CLMST.Prop247StandardCone
public import SerrePositivity.CLMST.Prop247Uniform
public import SerrePositivity.CLMST.IsogenyDescent
public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionFrobenius

/-! # Prop 2.4.7：指定した実 perfectoid 化から全段共通指数と降下

普遍対象の存在引用を使わず、指定した実写像に対して証明する。
残る実 almost 比較は明示入力とし、導来比較は標準四角形から構成する。
-/

@[expose] public noncomputable section
universe u
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
theorem prop247_uniform_of_standard_comparison
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
  let α := (prop247_completionMap p β hβ).toLinearMap
  let t := (IsScalarTower.toAlgHom B (B ⊗[R] S)
    (AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S))).toLinearMap
  have hα : α.comp t = β.toLinearMap := by
    ext x
    exact prop247_completionMap_unit p β hβ x
  apply prop247_uniform_of_common_comparison (algebraMap R B) (p : R) g f.toLinearMap
    r β.toLinearMap u v w hsq hu hv hw hcw t
    (prop247_tensor_completion_unit_surjective B p R S hB) α hα
  intro n
  simpa only [map_natCast] using prop247_standardReductionConeIso R S B C P p hR hB
    f hf β hβ hflat N hN n

/-- 指定した元の実 perfectoid 化写像の錐・核・余核へ共通指数を忠実降下する。 -/
theorem prop247_isogeny_of_standard_comparison
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B))) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
      (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ x : C ⧸ f.toLinearMap.range, g ^ q • x = 0) := by
  exact moduleMapConeIsogeny_descent (algebraMap R B) (p : R) hflat f.toLinearMap
    (prop247_cone_isComplete_of_perfectoid_target R S p hR C hf.1 f.toLinearMap) g
    (prop247_uniform_of_standard_comparison R S B C P E p hR hB f hf hbounded g r β hβ
      u v w hsq hu hv hw hcw hflat.1)

end SerrePositivity.CLMST
