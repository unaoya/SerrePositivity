module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaAlgebra.PerfectPrismDeltaAlgebraPowerInputs
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteFlatReductionBounded
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionUpperBound
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity

/-! # 完全prism上の実δ完全化逐次対象の離散性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (E : DeltaStructure p B) (j : A →+* B)
variable (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
variable
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
    (hFF : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
local notation "d" => OrientedPrism.generator P
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j d
include hP hj hzero hFF

/-- 同じ実δ完全化逐次対象の生成元冪商は離散でH0は有界p冪ねじれを持つ。 -/
theorem perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion (n : ℕ) (hn : 0 < n) :
    let T := A ⧸ Ideal.span {d ^ n}
    let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ k : ℕ,
        ∀ z : (DerivedCategory.homologyFunctor (ModuleCat.{u} T) 0).obj Z.obj,
          (p : T) ^ k • z = 0 → (p : T) ^ N • z = 0 := by
  obtain ⟨hc, ht, hz, hf⟩ :=
    perfectPrismDeltaAlgebraCompletionPower_G9_inputs P E j n hP hj hzero hFF hn
  exact derived_pure_bounded_torsion_of_complete_flat_reduction _ _ hz hf ⟨n, ht⟩ hc

/-- 同じ生成元冪商の非零次数ホモロジーは零。 -/
theorem perfectPrismDeltaAlgebraCompletionPower_homology_isZero
    (n : ℕ) (hn : 0 < n) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {d ^ n})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X).obj) := by
  obtain ⟨hGE, hLE, _⟩ :=
    perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion P E j hP hj hzero hFF n hn
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 実δ完全化の生成元冪余核は、零冪を含め全負次数で消える。 -/
theorem perfectPrismDeltaAlgebraCompletion_powerCokernel_homology_isZero
    (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((powerCokernelComplex d (boundedAboveDerivedChosenModel X).complex n).homology i) := by
  apply powerCokernel_homology_isZero_of_reduction d n X i
  by_cases hn : 0 < n
  · exact perfectPrismDeltaAlgebraCompletionPower_homology_isZero
      P E j hP hj hzero hFF n hn i (by omega)
  · have hn0 : n = 0 := by omega
    subst n
    let : Subsingleton (A ⧸ Ideal.span {d ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact Module.subsingleton (A ⧸ Ideal.span {d ^ 0}) _

/-- 完全prism上の実δ完全化逐次対象は離散。 -/
theorem perfectPrismDeltaAlgebraCompletion_pure :
    (X).obj.IsGE 0 ∧ (X).obj.IsLE 0 := by
  have hmod (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {d})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj X).obj) := by
    let F (t : A) := IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {t})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {t}))).obj X).obj)
    exact Eq.mp (congrArg F (pow_one d))
      (perfectPrismDeltaAlgebraCompletionPower_homology_isZero
          P E j hP hj hzero hFF 1 (by omega) i hi)
  obtain ⟨hGE, hLE, _⟩ := derived_pure_of_complete_regular_quotient_pure d
    P.generator_regular X (deltaAlgebraPerfectionIteratedPDCompletion_isComplete_d E j d) hmod
  exact ⟨hGE, hLE⟩

/-- 同じ実δ完全化逐次対象をその実H0のsingleに正規化して同定する。 -/
def perfectPrismDeltaAlgebraCompletionSingleIso :
    (X).obj ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismDeltaAlgebraCompletion_pure P E j hP hj hzero hFF
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso (X).obj 0

end SerrePositivity.BhattScholze
