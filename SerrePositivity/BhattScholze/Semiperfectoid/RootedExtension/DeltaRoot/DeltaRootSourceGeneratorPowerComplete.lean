module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSourceGeneratorPowerReduction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative

/-! # G8による生成元冪商上のp導来完備性

既証の係数制限後の完備性を、元の標準単位の図式と同型反映で商環へ戻す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- 正則生成元の任意冪商への実還元は、その商環上でp導来完備。n=0も含む。 -/
theorem deltaRootSourceGeneratorPowerReduction_isComplete_over_quotient
    (hd : IsSMulRegular A d) (n : ℕ) :
    IsComplete (A ⧸ Ideal.span {d ^ n}) (p : A ⧸ Ideal.span {d ^ n})
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
        (DeltaRootSourceIteratedPDCompletion D d b)).obj := by
  let q := Ideal.Quotient.mk (Ideal.span {d ^ n})
  let T := A ⧸ Ideal.span {d ^ n}
  let Y := ((boundedAboveDerivedBaseChange q).obj
    (DeltaRootSourceIteratedPDCompletion D d b)).obj
  let F := derivedRestrictScalars q
  have hR : IsComplete A (p : A) (F.obj Y) :=
    deltaRootSourceGeneratorPowerReduction_isComplete_p D d b hd n
  have hunitR : IsIso ((derivedComplexCompletionUnit A (p : A)).app (F.obj Y)) :=
    derivedComplexCompletionUnit_isIso_of_isComplete A (p : A) (F.obj Y) hR
  let e := derivedRestrictionCompletionIso q (p : A)
  have hc : IsIso (F.map ((derivedComplexCompletionUnit T (q (p : A))).app Y) ≫
      e.hom.app Y) := by
    rw [derivedRestrictionCompletionIso_unit]
    exact hunitR
  have hm : IsIso (F.map ((derivedComplexCompletionUnit T (q (p : A))).app Y)) :=
    IsIso.of_isIso_comp_right _ (e.hom.app Y)
  have hS : IsIso ((derivedComplexCompletionUnit T (q (p : A))).app Y) :=
    isIso_of_reflects_iso _ F
  have hcomplete := (isComplete_iff_derivedComplexCompletionUnit_isIso T (q (p : A)) Y).mpr hS
  simpa only [map_natCast] using hcomplete

end SerrePositivity.BhattScholze
