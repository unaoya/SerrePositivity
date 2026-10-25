module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.PerfectPrismRootPowerDiscrete
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.Source.DeltaRootSourceCompletionH0
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSourceIteratedCompletionComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity

/-! # 完全prism上の任意根族の元の実逐次源の離散性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "X" => DeltaRootSourceIteratedPDCompletion D d b
include hP

/-- 同じ元の実逐次源の生成元冪余核は、零冪も含め全負次数で消える。 -/
theorem perfectPrismRootSource_powerCokernel_homology_isZero
    (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((powerCokernelComplex d (boundedAboveDerivedChosenModel X).complex n).homology i) := by
  apply powerCokernel_homology_isZero_of_reduction d n X i
  by_cases hn : 0 < n
  · exact perfectPrismRootPower_homology_isZero P hP b n hn i (by omega)
  · have hn0 : n = 0 := by omega
    subst n
    let : Subsingleton (A ⧸ Ideal.span {d ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact Module.subsingleton (A ⧸ Ideal.span {d ^ 0}) _

/-- 完全prism上の任意根族の元の実p,d逐次完備化源は離散。 -/
theorem perfectPrismRootSource_pure :
    (X).obj.IsGE 0 ∧ (X).obj.IsLE 0 := by
  have hmod (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {d})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj X).obj) := by
    let F (t : A) := IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {t})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {t}))).obj X).obj)
    exact Eq.mp (congrArg F (pow_one d))
      (perfectPrismRootPower_homology_isZero P hP b 1 (by omega) i hi)
  obtain ⟨hGE, hLE, _⟩ := derived_pure_of_complete_regular_quotient_pure d
    P.generator_regular X (deltaRootSourceIteratedPDCompletion_isComplete_d D d b) hmod
  exact ⟨hGE, hLE⟩

/-- 元の実逐次源の非零次数ホモロジーは全て消える。 -/
theorem perfectPrismRootSource_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismRootSource_pure P hP b
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 離散性により、元の実逐次源をその実H0のsingle対象と同定する。 -/
def perfectPrismRootSourceSingleIso :
    (X).obj ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismRootSource_pure P hP b
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso (X).obj 0

/-- このsingle比較は同じ実H0上で恒等写像に正規化されている。 -/
theorem perfectPrismRootSourceSingleIso_homologyZero :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (perfectPrismRootSourceSingleIso P hP b).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).hom.app
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (X).obj) = 𝟙 _ := by
  obtain ⟨hGE, hLE⟩ := perfectPrismRootSource_pure P hP b
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso_homology (X).obj 0

end SerrePositivity.BhattScholze
