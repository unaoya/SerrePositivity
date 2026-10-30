module

public import SerrePositivity.CLMST.Prop247BaseChange
public import SerrePositivity.CLMST.Prop247Uniform
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators

/-! # Prop 2.4.7：元の標準射への条件付き合流

局所的な実有限自由比較と実 almost 比較、完備導来底変換の全剰余比較を
明示入力にして既存 D1〜D6 へ渡す。これらの存在を主張せず、引用を置換しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

/-- 原典の元の perfectoid 化写像に対する条件付き降下。
一つの局所比較に対する入口であり、被覆・rank 還元は別途必要。 -/
theorem prop247_isogeny_of_common_comparison
    (R S B C E : Type u) [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra B C]
    [AddCommGroup E] [Module B E]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hB : IsIntegralPerfectoid B p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B)))
    (g : R) (r : ℕ) (β : B ⊗[R] S →ₐ[B] C)
    (hβ : IsPerfectoidization p β.toRingHom)
    (u : (B ⊗[R] S) →ₗ[B] (Fin r → B))
    (v : C →ₗ[B] E) (w : (Fin r → B) →ₗ[B] E)
    (hsq : v.comp β.toLinearMap = w.comp u)
    (hu : Function.Bijective (awayModuleMap (algebraMap R B g) u))
    (hv : ∀ y : C, v y = 0 → algebraMap R B g • y = 0)
    (hw : ∀ z : (Fin r → B), w z = 0 → algebraMap R B g • z = 0)
    (hcw : ∀ y : E ⧸ w.range, algebraMap R B g • y = 0)
    (comparison : ∀ n : ℕ,
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        ((boundedAboveDerivedScalarCone R ((p : R) ^ n)).obj
          (moduleMapConeBoundedAbove (perfectoidizationModuleMap R S p hR)))).obj ≅
      (derivedScalarConeFunctor B ((p : B) ^ n)).obj
        (moduleMapCone B (prop247_completionMap p β hβ).toLinearMap)) :
    ∃ N : ℕ, moduleMapConeScalar R (perfectoidizationModuleMap R S p hR) (g ^ N) = 0 ∧
      (∀ x : (perfectoidizationModuleMap R S p hR).ker, g ^ N • x = 0) ∧
      (∀ x : Perfectoidization R S p hR ⧸
        (perfectoidizationModuleMap R S p hR).range, g ^ N • x = 0) := by
  let := hB.isReduced B p
  let := Module.FinitePresentation.of_finite_of_finitePresentation R S
  let α := (prop247_completionMap p β hβ).toLinearMap
  let t := (IsScalarTower.toAlgHom B (B ⊗[R] S)
    (AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S))).toLinearMap
  have hα : α.comp t = β.toLinearMap := by
    ext x
    exact prop247_completionMap_unit p β hβ x
  have hU := prop247_uniform_of_common_comparison (algebraMap R B) (p : R) g
    (perfectoidizationModuleMap R S p hR) r β.toLinearMap u v w hsq hu hv hw hcw
    t (prop247_tensor_completion_unit_surjective B p R S hB) α hα
    (fun n => by simpa only [map_natCast] using comparison n)
  exact moduleMapConeIsogeny_descent (algebraMap R B) (p : R) hflat
    (perfectoidizationModuleMap R S p hR) (prop247_cone_isComplete R S p hR) g hU

end SerrePositivity.CLMST
