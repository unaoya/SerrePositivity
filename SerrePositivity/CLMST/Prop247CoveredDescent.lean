module

public import SerrePositivity.CLMST.Prop247UniformStandard
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators

/-! # Prop 2.4.7：底変換先の実有限被覆から元の写像への降下

被覆の元は底変換先 B に属してよく、元の R の元の像である必要はない。
大域的な一つの有限自由比較を仮定しない。
-/

@[expose] public noncomputable section
universe u
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
theorem prop247_uniform_of_standard_fixed_cone
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
  let α := (prop247_completionMap p β hβ).toLinearMap
  let t := (IsScalarTower.toAlgHom B (B ⊗[R] S)
    (AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S))).toLinearMap
  have hα : α.comp t = β.toLinearMap := by
    ext x
    exact prop247_completionMap_unit p β hβ x
  apply prop247_uniform_reductions_of_fixed_cone (algebraMap R B) (p : R) g f.toLinearMap α
    ⟨2 * q, moduleMapConeScalar_of_surjective_source t
      (prop247_tensor_completion_unit_surjective B p R S hB) α β.toLinearMap hα
      (algebraMap R B g) q hq⟩
  intro n
  simpa only [map_natCast] using prop247_standardReductionConeIso R S B C P p hR hB
    f hf β hβ hflat N hN n

/-- 実有限被覆上の β の錐零化を合流し、全段共通指数を介して元の f へ降下する。
各被覆部分に同じ rank や同じ局所指数を要求しない。 -/
theorem prop247_isogeny_of_standard_finite_cover
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
    (prop247_cone_isComplete_of_perfectoid_target R S p hR C hf.1 f.toLinearMap) g
    (prop247_uniform_of_standard_fixed_cone R S B C P p hR hB f hf hbounded g β hβ hflat.1 hfixed)

end SerrePositivity.CLMST
