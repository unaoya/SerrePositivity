module

public import SerrePositivity.BhattScholze.DeltaRootPerfectionFaithful
public import SerrePositivity.BhattScholze.PerfectOrientedPrism

/-! # 完全prismから任意根族のraw平坦包と実p完備化への入口 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard deltaRootRawCoefficientAlgebra
  deltaRootPerfectionAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "R" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" =>
  DeltaAdjoinDivision E (p : R) (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "qA" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "X" => CategoryTheory.Functor.obj
  (DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A))
  (CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor (ModuleCat.of A B))
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qA) X

include hP in
private theorem delta_p_unit : DeltaStructure.IsDistinguished D (p : A) := by
  let := P.isAdicComplete_p_of_perfect hP
  exact DeltaStructure.isDistinguished_p D
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)})
      (Ideal.mem_span_singleton_self _))

include hP in
/-- 完全prismの任意元族に対するraw p除算包は、元の係数環上p完全忠実平坦。 -/
theorem perfectPrismRootRaw_isCompletelyFaithfullyFlat :
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A)}) B := by
  obtain ⟨w, hw⟩ := delta_p_unit P hP
  exact deltaRootFamilyRaw_isCompletelyFaithfullyFlat D b hP.p_mul_injective w hw

/-- 具体的raw包の元の係数環上の実p完備化はp導来完備。 -/
theorem perfectPrismRootRawCompletion_isComplete :
    DerivedCompletion.IsComplete A (p : A) (X).obj :=
  DerivedCompletion.derivedComplexCompletionFunctor_isComplete A (p : A)
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)).obj

include hP in
/-- G9へ渡す、完全prism上の具体的実完備化の標準mod p次数消滅・H0忠実平坦性。 -/
theorem perfectPrismRootRawCompletion_modP_pure_faithfullyFlat :
    (∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat QA) i).obj (Y).obj)) ∧
      Module.FaithfullyFlat QA
        ((DerivedCategory.homologyFunctor (ModuleCat QA) 0).obj (Y).obj) := by
  obtain ⟨w, hw⟩ := delta_p_unit P hP
  exact ⟨deltaRootFamilyCompletedModP_homology_isZero_of_p_regular D b hP.p_mul_injective w hw,
    deltaRootFamilyCompletedModPH0_faithfullyFlat_of_p_regular D b hP.p_mul_injective w hw⟩

include hP in
/-- 完全prismの任意元族raw包の実δ完全化は、追加単元仮定なしにp完全忠実平坦。 -/
theorem perfectPrismRootPerfection_isCompletelyFaithfullyFlat :
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A)})
      (DeltaPerfection (deltaAdjoinDivisionStructure E (p : R)
        (fun s ↦ DeltaStructure.frobeniusLift E (r s)))) := by
  obtain ⟨w, hw⟩ := delta_p_unit P hP
  exact deltaRootPerfection_isCompletelyFaithfullyFlat D b hP w hw

end SerrePositivity.BhattScholze
