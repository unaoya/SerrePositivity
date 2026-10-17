module

public import SerrePositivity.CLMST.Prop247Conditional
public import SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange
public import SerrePositivity.CLMST.Prop247ConeComparison

/-! # Prop 2.4.7：一つの完備導来錐比較からの降下

各剰余段の比較を個別の仮定にせず、実完備底変換の一つの錐比較から構成する。
この最後の錐比較と実 almost 比較の存在は、引き続き明示入力である。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

/-- 元の標準写像の完備導来底変換の実錐比較一つで、全段を一様に降下できる。 -/
theorem prop247_isogeny_of_completed_comparison
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
    (comparison : (derivedComplexCompletionFunctor B (p : B)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (moduleMapConeBoundedAbove (perfectoidizationModuleMap R S p hR))).obj ≅
      moduleMapCone B (prop247_completionMap p β hβ).toLinearMap) :
    ∃ N : ℕ, moduleMapConeScalar R (perfectoidizationModuleMap R S p hR) (g ^ N) = 0 ∧
      (∀ x : (perfectoidizationModuleMap R S p hR).ker, g ^ N • x = 0) ∧
      (∀ x : Perfectoidization R S p hR ⧸
        (perfectoidizationModuleMap R S p hR).range, g ^ N • x = 0) := by
  apply prop247_isogeny_of_common_comparison R S B C E p hR hB hflat g r β hβ
    u v w hsq hu hv hw hcw
  intro n
  have e := boundedAboveDerivedBaseChangePowerConeCompletionIso (algebraMap R B) (p : R) n
    (moduleMapConeBoundedAbove (perfectoidizationModuleMap R S p hR))
  simp only [map_natCast] at e
  exact e ≪≫ (derivedScalarConeFunctor B ((p : B) ^ n)).mapIso comparison

/-- 始域・終域の実同型と元の標準射の可換四角形から、元の Prop 2.4.7 の錐へ降下する。
錐の同型や各剰余段の同型を追加の入力にはしない。 -/
theorem prop247_isogeny_of_standard_square
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
    (eS : (derivedComplexCompletionFunctor B (p : B)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B
        (AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S))))
    (eC : (derivedComplexCompletionFunctor B (p : B)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R (Perfectoidization R S p hR)))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B C))
    (hsquare : (derivedComplexCompletionFunctor B (p : B)).map
        ((boundedAboveDerivedBaseChange (algebraMap R B)).map
          (boundedAboveDerivedSingleFunctor.map
            (ModuleCat.ofHom (perfectoidizationModuleMap R S p hR)))).hom ≫ eC.hom =
      eS.hom ≫ (moduleObjectFunctor B).map
        (ModuleCat.ofHom (prop247_completionMap p β hβ).toLinearMap)) :
    ∃ N : ℕ, moduleMapConeScalar R (perfectoidizationModuleMap R S p hR) (g ^ N) = 0 ∧
      (∀ x : (perfectoidizationModuleMap R S p hR).ker, g ^ N • x = 0) ∧
      (∀ x : Perfectoidization R S p hR ⧸
        (perfectoidizationModuleMap R S p hR).range, g ^ N • x = 0) := by
  apply prop247_isogeny_of_completed_comparison R S B C E p hR hB hflat g r β hβ
    u v w hsq hu hv hw hcw
  have e := prop247_completedModuleConeIso (algebraMap R B) (p : R)
    (perfectoidizationModuleMap R S p hR) (prop247_completionMap p β hβ).toLinearMap
  rw [map_natCast] at e
  exact e eS eC hsquare

end SerrePositivity.CLMST
