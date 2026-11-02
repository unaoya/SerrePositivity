module

public import SerrePositivity.CLMST.Prop247StandardSquare
public import SerrePositivity.CLMST.Prop247ConeComparison
public import SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange

/-! # Prop 2.4.7：標準四角形から実錐と全剰余段への比較

始域・終域・四角形を未知の仮定として受けず、証明済みの実標準比較を用いる。
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
    (β : B ⊗[R] S →ₐ[B] P) (hβ : IsPerfectoidization p β.toRingHom)
    (hflat : IsCompletelyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B)))
    (N : ℕ) (hbounded : ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)

/-- 元の射の実完備底変換錐は、原典の α の実加群錐と同型。 -/
def prop247_standardCompletedConeIso :
    (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (moduleMapConeBoundedAbove f.toLinearMap)).obj ≅
      moduleMapCone B (prop247_completionMap p β hβ).toLinearMap :=
  prop247_completedModuleConeIso (algebraMap R B) (p : R) f.toLinearMap
    (prop247_completionMap p β hβ).toLinearMap
    (prop247_sourceCompletedAdicIso R S B p hB hflat N hbounded)
    (BhattScholze.targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ)
    (prop247_completedBaseChange_adic_standard_square R S B C P p hR hB f hf β hβ
      hflat N hbounded)

/-- 実錐の比較は元の三角形の標準の右包含を保つ。 -/
theorem prop247_standardCompletedConeIso_inclusion :
    (prop247_completedModuleTriangle (algebraMap R B) (p : R) f.toLinearMap).mor₂ ≫
      (prop247_standardCompletedConeIso R S B C P p hR hB f hf β hβ hflat N hbounded).hom =
    (BhattScholze.targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ).hom ≫
      (moduleMapConeTriangle B (prop247_completionMap p β hβ).toLinearMap).mor₂ :=
  prop247_completedModuleConeIso_inclusion (algebraMap R B) (p : R) f.toLinearMap
    (prop247_completionMap p β hβ).toLinearMap
    (prop247_sourceCompletedAdicIso R S B p hB hflat N hbounded)
    (BhattScholze.targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ)
    (prop247_completedBaseChange_adic_standard_square R S B C P p hR hB f hf β hβ
      hflat N hbounded)

/-- 全ての冪剰余段の実底変換を、原典の α の実錐の冪剰余へ比較する。 -/
def prop247_standardReductionConeIso (n : ℕ) :
    ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
      ((boundedAboveDerivedScalarCone R ((p : R) ^ n)).obj
        (moduleMapConeBoundedAbove f.toLinearMap))).obj ≅
    (derivedScalarConeFunctor B ((p : B) ^ n)).obj
      (moduleMapCone B (prop247_completionMap p β hβ).toLinearMap) := by
  have e := boundedAboveDerivedBaseChangePowerConeCompletionIso (algebraMap R B) (p : R) n
    (moduleMapConeBoundedAbove f.toLinearMap)
  rw [map_natCast] at e
  have c := prop247_standardCompletedConeIso R S B C P p hR hB f hf β hβ hflat N hbounded
  rw [map_natCast] at c
  exact e ≪≫ (derivedScalarConeFunctor B ((p : B) ^ n)).mapIso c

end SerrePositivity.CLMST
