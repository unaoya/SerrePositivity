module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaAlgebra.PerfectPrismDeltaAlgebraCompletionInputs
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative

/-! # 実δ完全化逐次対象の生成元冪商のp導来完備性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j d

/-- 同じ実δ完全化逐次対象の生成元冪商を、元の係数上の実Koszul錐へ比較する。 -/
def deltaAlgebraPerfectionGeneratorPowerReductionKoszulIso
    (hd : IsSMulRegular A d) (n : ℕ) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X)).obj ≅
        (derivedScalarConeFunctor A (d ^ n)).obj (X).obj :=
  restrictedDerivedQuotientKoszulIso (d ^ n) (hd.pow n) X

/-- 正則生成元の任意冪商への同じ実還元は、その商環上でp導来完備。 -/
theorem deltaAlgebraPerfectionGeneratorPowerReduction_isComplete_over_quotient
    (hd : IsSMulRegular A d) (n : ℕ) :
    IsComplete (A ⧸ Ideal.span {d ^ n}) (p : A ⧸ Ideal.span {d ^ n})
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X).obj := by
  let q := Ideal.Quotient.mk (Ideal.span {d ^ n})
  let T := A ⧸ Ideal.span {d ^ n}
  let Y := ((boundedAboveDerivedBaseChange q).obj X).obj
  let F := derivedRestrictScalars q
  have hR : IsComplete A (p : A) (F.obj Y) := by
    let K := DerivedCategory.Q.objPreimage (X).obj
    let eK : DerivedCategory.Q.obj K ≅ (X).obj := DerivedCategory.Q.objObjPreimageIso (X).obj
    have hK : IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
      isComplete_of_iso A (p : A) eK.symm
        (deltaAlgebraPerfectionIteratedPDCompletion_isComplete_p E j d)
    have hC := isComplete_Q_mappingCone A (p : A) (smulId (d ^ n) K) hK hK
    let e := deltaAlgebraPerfectionGeneratorPowerReductionKoszulIso E j d hd n ≪≫
      (derivedScalarConeFunctor A (d ^ n)).mapIso eK.symm ≪≫
        (derivedScalarConeComparison A (d ^ n)).app K
    exact isComplete_of_iso A (p : A) e.symm hC
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
