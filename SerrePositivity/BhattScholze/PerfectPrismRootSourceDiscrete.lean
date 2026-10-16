module

public import SerrePositivity.BhattScholze.PerfectPrismRootPowerDiscrete
public import SerrePositivity.BhattScholze.DeltaRootSourceCompletionH0
public import SerrePositivity.BhattScholze.DeltaRootSourceIteratedCompletionComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator

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
  let K := boundedAboveDerivedChosenModel X
  have hK : ∀ i, Module.Flat A (K.complex.X i) := by
    intro i
    have : Module.Projective A (K.complex.X i) := inferInstance
    infer_instance
  have ht : ∀ n : ℕ, ∀ x : A, d ^ n * x = 0 → d ^ 0 * x = 0 := by
    intro n x hx
    have hd : IsSMulRegular A d := P.generator_regular
    have hr : Function.Injective (fun z : A => d ^ n * z) :=
      IsSMulRegular.pow n hd
    have hz : x = 0 := hr (by simpa using hx)
    simp [hz]
  have hc := isComplete_of_iso A d K.iso.symm
    (deltaRootSourceIteratedPDCompletion_isComplete_d D d b)
  have := powerCokernelReconstruction_quasiIso d K.complex hK 0 ht hc
  refine ⟨(DerivedCategory.isGE_iff _ _).mpr ?_,
    deltaRootSourceIteratedPDCompletion_isLE_zero D d b⟩
  intro i hi
  have hz : IsZero ((complexTowerHomotopyLimit A
      (powerCokernelComplex d K.complex)
      (powerCokernelComplexTransition d K.complex)).homology i) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun x y => sub_eq_zero.mp ?_⟩
    simpa only [one_mul, one_smul] using
      complexTowerHomotopyLimit_homology_annihilated A
        (powerCokernelComplex d K.complex) (powerCokernelComplexTransition d K.complex) i 1 1
        (fun n _ => (ModuleCat.isZero_iff_subsingleton.mp
          (perfectPrismRootSource_powerCokernel_homology_isZero P hP b n i hi)).elim _ _)
        (fun n _ => (ModuleCat.isZero_iff_subsingleton.mp
          (perfectPrismRootSource_powerCokernel_homology_isZero
            P hP b n (i - 1) (by omega))).elim _ _)
        (x - y)
  have hzK := hz.of_iso (asIso (homologyMap (powerCokernelReconstruction d K.complex) i))
  exact hzK.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso K.iso.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app K.complex)

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
