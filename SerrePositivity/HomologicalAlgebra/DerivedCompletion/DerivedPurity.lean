module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTower
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.PerfectRingTor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import SerrePositivity.HomologicalAlgebra.DerivedH0Algebra

/-! # 導来完備対象の純性

## 概要

導来完備でスカラーの錐が零次に集中すれば、元の対象は離散で H⁰ へのスカラーの作用が単射である（`derived_homology_smul_injective_of_scalarCone_isZero` ほか）。有界ねじれの環の上の完備で平坦な主元簡約から純性と有界な冪ねじれを（`derived_pure_bounded_torsion_of_complete_flat_reduction`）、射影模型で通常の冪の余核が導来簡約を計算すること、完備対象の標準 Koszul 再構成による一様な零化、完全な mod p の剰余を持つ完備テンソル積の純性（`completedTensor_pure_of_perfect_residue`）を与える。

## 方針

平坦性・有限性・有界性・環の正則性は、純性の判定には仮定しない。

## 規約

旧 `CompleteScalarConePurity`・`CompleteFlatReductionPure`・`CompleteFlatReductionBounded`・`DerivedPowerCokernelModel`・`CompleteMilnorAnnihilator`・`PerfectResidueCompletedTensor`。

## 使われ方

BhattScholze（Almost・Prism・Perfectoidization）。
-/

@[expose] public noncomputable section

universe u

section CompleteScalarConePurityPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)

/-- A complete module on which the completion scalar is surjective is zero. -/
lemma isZero_of_complete_of_smul_surjective (M : ModuleCat.{u} R)
    (hc : IsModuleComplete R a M) (hs : Function.Surjective (fun x : M => a • x)) :
    IsZero M := by
  have h := linearMap_eq_zero_of_smul_surjective_of_isModuleComplete a M M hs hc
    (LinearMap.id : M →ₗ[R] M)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  exact congrArg (fun f : M →ₗ[R] M => f x) h

/-- Vanishing of scalar-cone homology gives surjectivity on the original homology. -/
lemma cochain_homology_smul_surjective_of_scalarCone_isZero
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (h : IsZero (((scalarConeFunctor a).obj K).homology i)) :
    Function.Surjective (fun x : K.homology i => a • x) := by
  have he := Cone.exact₂ (smulId a K) i
  have hm : Epi (homologyMap (smulId a K) i) :=
    he.epi_f (h.eq_zero_of_tgt _)
  have hs := (ModuleCat.epi_iff_surjective _).mp hm
  simp only [smulId, homologyMap_smul, homologyMap_id] at hs
  exact hs

/-- Vanishing in the previous scalar-cone degree gives injectivity on homology. -/
lemma cochain_homology_smul_injective_of_scalarCone_isZero
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (h : IsZero (((scalarConeFunctor a).obj K).homology (i - 1))) :
    Function.Injective (fun x : K.homology i => a • x) := by
  have he := Cone.exact₁ (smulId a K) (i - 1) i (by omega)
  have hm : Mono (homologyMap (smulId a K) i) :=
    he.mono_g (h.eq_zero_of_src _)
  have hs := (ModuleCat.mono_iff_injective _).mp hm
  simp only [smulId, homologyMap_smul, homologyMap_id] at hs
  exact hs

/-- The surjectivity statement on the original actual derived homology. -/
lemma derived_homology_smul_surjective_of_scalarCone_isZero
    (X : ConcreteDerivedCategory R) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X))) :
    Function.Surjective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X => a • x) := by
  let K := DerivedCategory.Q.objPreimage X
  let eX := DerivedCategory.Q.objObjPreimageIso X
  let eH : K.homology i ≅ (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso eX
  let ec := ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app
      ((scalarConeFunctor a).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      ((derivedScalarConeComparison R a).symm.app K ≪≫
        (derivedScalarConeFunctor R a).mapIso eX)
  have hs := cochain_homology_smul_surjective_of_scalarCone_isZero a K i (h.of_iso ec)
  intro x
  obtain ⟨y, hy⟩ := hs (eH.toLinearEquiv.symm x)
  refine ⟨eH.toLinearEquiv y, ?_⟩
  change a • eH.toLinearEquiv y = x
  change a • y = eH.toLinearEquiv.symm x at hy
  rw [← eH.toLinearEquiv.map_smul, hy, eH.toLinearEquiv.apply_symm_apply]

/-- The injectivity statement on the original actual derived homology. -/
lemma derived_homology_smul_injective_of_scalarCone_isZero
    (X : ConcreteDerivedCategory R) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (i - 1)).obj
      ((derivedScalarConeFunctor R a).obj X))) :
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X => a • x) := by
  let K := DerivedCategory.Q.objPreimage X
  let eX := DerivedCategory.Q.objObjPreimageIso X
  let eH : K.homology i ≅ (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso eX
  let ec := ((DerivedCategory.homologyFunctorFactors (ModuleCat R) (i - 1)).app
      ((scalarConeFunctor a).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) (i - 1)).mapIso
      ((derivedScalarConeComparison R a).symm.app K ≪≫
        (derivedScalarConeFunctor R a).mapIso eX)
  have hs := cochain_homology_smul_injective_of_scalarCone_isZero a K i (h.of_iso ec)
  intro x y hxy
  apply eH.toLinearEquiv.symm.injective
  apply hs
  change a • eH.toLinearEquiv.symm x = a • eH.toLinearEquiv.symm y
  change a • x = a • y at hxy
  rw [← eH.toLinearEquiv.symm.map_smul, ← eH.toLinearEquiv.symm.map_smul, hxy]

/-- A complete homology module vanishes when the same scalar-cone homology vanishes. -/
lemma derived_homology_isZero_of_complete_of_scalarCone_isZero
    (X : ConcreteDerivedCategory R) (hc : IsComplete R a X) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X) :=
  isZero_of_complete_of_smul_surjective a _ (isComplete_homology_isModuleComplete R a X hc i)
    (derived_homology_smul_surjective_of_scalarCone_isZero a X i h)

/-- A complete object with discrete Koszul reduction is discrete, with regular H0 action. -/
lemma derived_pure_of_complete_scalarCone_pure
    (X : ConcreteDerivedCategory R) (hc : IsComplete R a X)
    (h : ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X))) :
    X.IsGE 0 ∧ X.IsLE 0 ∧
      Function.Injective
        (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X => a • x) := by
  have hz (i : ℤ) (hi : i ≠ 0) :=
    derived_homology_isZero_of_complete_of_scalarCone_isZero a X hc i (h i hi)
  exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i hi => hz i (by omega)),
    (DerivedCategory.isLE_iff _ _).mpr (fun i hi => hz i (by omega)),
    derived_homology_smul_injective_of_scalarCone_isZero a X 0 (by simpa using h (-1) (by omega))⟩

/-- For a regular scalar on R, an ordinary derived quotient can detect the same purity. -/
lemma derived_pure_of_complete_regular_quotient_pure
    (ha : IsSMulRegular R a) (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hc : IsComplete R a X.obj)
    (h : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj)) :
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧
      Function.Injective
        (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => a • x) := by
  apply derived_pure_of_complete_scalarCone_pure a X.obj hc
  intro i hi
  let q := Ideal.Quotient.mk (Ideal.span {a})
  let Y := (boundedAboveDerivedBaseChange q).obj X
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      (restrictedDerivedQuotientKoszulIso a ha X).symm ≪≫
    (derivedRestrictScalarsHomologyIso q i).app Y.obj
  exact ((ModuleCat.restrictScalars q).map_isZero (h i hi)).of_iso e
end SerrePositivity.DerivedCompletion

end CompleteScalarConePurityPart

section DerivedPowerCokernelModelPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)

/-- The standard quotient's original R-action agrees with restriction along
the actual quotient homomorphism. -/
def powerQuotientCoefficientIso (n : ℕ) :
    ModuleCat.of R (R ⧸ Ideal.span {a ^ n}) ≅
      baseChangeScalarModule (Ideal.Quotient.mk (Ideal.span {a ^ n})) :=
  (LinearEquiv.refl R (R ⧸ Ideal.span {a ^ n})).toModuleIso

/-- Actual derived reduction, restricted to R, is the ordinary cokernel of
a^n on the chosen projective model, without any regularity assumption. -/
def derivedPowerCokernelModelIso (n : ℕ) (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X)).obj ≅
        DerivedCategory.Q.obj
          (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n) :=
  restrictedDerivedBaseChangeModelIso (Ideal.Quotient.mk (Ideal.span {a ^ n})) X ≪≫
    DerivedCategory.Q.mapIso (cochainTensorSingleLeftIso
      (baseChangeScalarModule (Ideal.Quotient.mk (Ideal.span {a ^ n})))
      (boundedAboveDerivedChosenModel X).complex) ≪≫
    DerivedCategory.Q.mapIso ((moduleTensorCochainFunctor
      (boundedAboveDerivedChosenModel X).complex).mapIso (powerQuotientCoefficientIso a n).symm) ≪≫
    DerivedCategory.Q.mapIso (powerCokernelTensorModelIso a
      (boundedAboveDerivedChosenModel X).complex (fun i ↦ by
        have : Module.Projective R ((boundedAboveDerivedChosenModel X).complex.X i) := inferInstance
        infer_instance) n).symm

/-- Homology of the actual power reduction is computed by the same cokernel model
in every degree, with its original restricted coefficient action. -/
def derivedPowerCokernelHomologyIso (n : ℕ) (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ) :
    (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology i ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a ^ n})) i).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj) :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      (derivedPowerCokernelModelIso a n X).symm ≪≫
    (derivedRestrictScalarsHomologyIso (Ideal.Quotient.mk (Ideal.span {a ^ n})) i).app _

lemma powerCokernel_homology_isZero_of_reduction (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a ^ n})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj)) :
    IsZero ((powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology i) :=
  (derivedPowerCokernelHomologyIso a n X i).isZero_iff.mpr
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {a ^ n}))).map_isZero h)

end SerrePositivity.DerivedCompletion

end DerivedPowerCokernelModelPart

section CompleteFlatReductionPurePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
include hPure hFlat

lemma powerCokernel_homology_isZero_of_flat_reduction (n : ℕ) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology i) := by
  obtain ⟨hGE, hLE, _⟩ := derived_power_reduction_pure_flat a X hPure hFlat n
  apply powerCokernel_homology_isZero_of_reduction a n X i
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- All homology differences are surjective, using the actual H0 quotient transitions. -/
lemma powerCokernelHomologyDifference_surjective (i : ℤ) :
    Function.Surjective (complexTowerHomologyDifference R
      (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex)
      (powerCokernelComplexTransition a (boundedAboveDerivedChosenModel X).complex) i) := by
  apply moduleTowerDifference_surjective
  intro n
  by_cases hi : i = 0
  · subst i
    exact powerCokernel_homology_zero_transition_surjective a X hPure hFlat n
  · intro y
    have hz := powerCokernel_homology_isZero_of_flat_reduction a X hPure hFlat n i hi
    exact ⟨0, (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _⟩

lemma powerCokernel_holim_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((complexTowerHomotopyLimit R
      (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex)
      (powerCokernelComplexTransition a
        (boundedAboveDerivedChosenModel X).complex)).homology i) := by
  have hinj := complexTowerMilnorProjection_injective_of_surjective R _ _ i
    (powerCokernelHomologyDifference_surjective a X hPure hFlat (i - 1))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ hinj ?_⟩
  apply Subtype.ext
  funext n
  exact (ModuleCat.isZero_iff_subsingleton.mp
    (powerCokernel_homology_isZero_of_flat_reduction a X hPure hFlat n i hi)).elim _ _

/-- The actual H0 is the inverse limit of the ordinary power-reduction H0 modules. -/
def completeFlatReductionH0LimitIso
    (hR : ∃ N : ℕ, ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a X.obj) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj ≅
      ModuleCat.of R (moduleTowerLimit R
        (fun n ↦ (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology 0)
        (fun n ↦ (homologyMap
          (powerCokernelComplexTransition a
            (boundedAboveDerivedChosenModel X).complex n) 0).hom)) := by
  let P := boundedAboveDerivedChosenModel X
  have hP : ∀ i, Module.Flat R (P.complex.X i) := by
    intro i
    have : Module.Projective R (P.complex.X i) := inferInstance
    infer_instance
  let N := Classical.choose hR
  have hN := Classical.choose_spec hR
  have hcP := isComplete_of_iso R a P.iso.symm hc
  have := powerCokernelReconstruction_quasiIso a P.complex hP N hN hcP
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso P.iso.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).app P.complex ≪≫
    asIso (homologyMap (powerCokernelReconstruction a P.complex) 0) ≪≫
    (complexTowerMilnorProjectionEquiv R _ _ 0
      (powerCokernelHomologyDifference_surjective a X hPure hFlat (-1))).toModuleIso

/-- G9 purity: no regularity, finite generation, Noetherianity, or classical completeness. -/
theorem derived_pure_of_complete_flat_reduction
    (hR : ∃ N : ℕ, ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a X.obj) : X.obj.IsGE 0 ∧ X.obj.IsLE 0 := by
  let P := boundedAboveDerivedChosenModel X
  have hP : ∀ i, Module.Flat R (P.complex.X i) := by
    intro i
    have : Module.Projective R (P.complex.X i) := inferInstance
    infer_instance
  obtain ⟨N, hN⟩ := hR
  have hcP := isComplete_of_iso R a P.iso.symm hc
  have := powerCokernelReconstruction_quasiIso a P.complex hP N hN hcP
  have hX (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X.obj) := by
    have hz := powerCokernel_holim_homology_isZero a X hPure hFlat i hi
    have hpz := hz.of_iso (asIso (homologyMap (powerCokernelReconstruction a P.complex) i))
    exact hpz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso P.iso.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P.complex)
  exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i hi ↦ hX i (by omega)),
    (DerivedCategory.isLE_iff _ _).mpr (fun i hi ↦ hX i (by omega))⟩

end SerrePositivity.DerivedCompletion

end CompleteFlatReductionPurePart

section CompleteFlatReductionBoundedPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))

/-- The actual ordinary power-reduction H0 is killed by that power. -/
lemma powerCokernelH0_power_annihilated (n : ℕ)
    (z : (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology 0) :
    a ^ n • z = 0 := by
  let e := (derivedPowerCokernelHomologyIso a n X 0).toLinearEquiv
  apply e.injective
  rw [map_smul, map_zero]
  change Ideal.Quotient.mk (Ideal.span {a ^ n}) (a ^ n) • e z = 0
  rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _), zero_smul]

variable
    (hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
include hPure hFlat

/-- Transfer the flat quotient relation through the actual R-linear homology comparison. -/
lemma powerCokernelH0_torsion_relation (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) (j m : ℕ)
    (z : (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex (j + m)).homology 0)
    (hz : a ^ m • z = 0) :
    ∃ y : (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex (j + m)).homology 0,
      a ^ N • z = a ^ j • y := by
  let q := Ideal.Quotient.mk (Ideal.span {a ^ (j + m)})
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a ^ (j + m)})) 0).obj
    ((boundedAboveDerivedBaseChange q).obj X).obj
  let e := (derivedPowerCokernelHomologyIso a (j + m) X 0).toLinearEquiv
  have hF : Module.Flat (R ⧸ Ideal.span {a ^ (j + m)}) H :=
    (derived_power_reduction_pure_flat a X hPure hFlat (j + m)).2.2
  let := hF
  have hzm : q a ^ m • (e z : H) = 0 := by
    have hez := congrArg e hz
    rw [map_smul, map_zero] at hez
    change q (a ^ m) • (e z : H) = 0 at hez
    simpa only [map_pow] using hez
  obtain ⟨y, hy⟩ := flat_powerQuotient_torsion_relation a N h j m H (e z) hzm
  refine ⟨e.symm y, ?_⟩
  apply e.injective
  rw [map_smul, map_smul, LinearEquiv.apply_symm_apply]
  change q (a ^ N) • (e z : H) = q (a ^ j) • y
  simpa only [map_pow] using hy

/-- G9 in the full requested generality, strengthened from natural primes to
arbitrary principal elements. The bound on H0 can be the original ring bound. -/
theorem derived_pure_bounded_torsion_of_complete_flat_reduction
    (hR : ∃ N : ℕ, ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a X.obj) :
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ n : ℕ,
        ∀ z : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj,
          a ^ n • z = 0 → a ^ N • z = 0 := by
  obtain ⟨hGE, hLE⟩ := derived_pure_of_complete_flat_reduction a X hPure hFlat hR hc
  obtain ⟨N, hN⟩ := hR
  let P := (boundedAboveDerivedChosenModel X).complex
  let M : ℕ → Type u := fun n ↦ (powerCokernelComplex a P n).homology 0
  let t := fun n ↦ (homologyMap (powerCokernelComplexTransition a P n) 0).hom
  have hLim := moduleTowerLimit_power_torsion_bound_of_relations a N M t
    (powerCokernelH0_power_annihilated a X)
    (powerCokernelH0_torsion_relation a X hPure hFlat N hN)
  let e := (completeFlatReductionH0LimitIso a X hPure hFlat ⟨N, hN⟩ hc).toLinearEquiv
  refine ⟨hGE, hLE, N, ?_⟩
  intro n z hz
  apply e.injective
  rw [map_smul, map_zero]
  apply hLim n (e z)
  rw [← map_smul, hz, map_zero]

end SerrePositivity.DerivedCompletion

end CompleteFlatReductionBoundedPart

section CompleteMilnorAnnihilatorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 任意の完備導来対象を、選ばれた代表複体の標準Koszul塔から再構成する。 -/
def completeDerivedKoszulHomotopyLimitIso (a : R) (X : ConcreteDerivedCategory R)
    (hX : IsComplete R a X) :
    X ≅ complexTowerHomotopyLimitObject R
      (complexPowerKoszulStage R a (DerivedCategory.Q.objPreimage X))
      (complexPowerKoszulTransition R a (DerivedCategory.Q.objPreimage X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  exact e.symm ≪≫ complexCompletionUnitIso R a K (isComplete_of_iso R a e.symm hX)

/-- 任意の完備導来対象に対する標準Koszul塔からの一様指数の移送。
指数Nは全段と隣接二次数に共通とし、比較同型は入力として要求しない。 -/
theorem completeDerived_homology_pow_annihilated (a : R) (X : ConcreteDerivedCategory R)
    (hX : IsComplete R a X) (i : ℤ) (g : R) (N : ℕ)
    (h : ∀ n,
      (∀ x : (complexPowerKoszulStage R a (DerivedCategory.Q.objPreimage X) n).homology i,
        g ^ N • x = 0) ∧
      (∀ x : (complexPowerKoszulStage R a (DerivedCategory.Q.objPreimage X) n).homology (i - 1),
        g ^ N • x = 0))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X) :
    g ^ (2 * N) • x = 0 :=
  derived_homology_pow_annihilated_of_iso_homotopyLimit R
    (complexPowerKoszulStage R a (DerivedCategory.Q.objPreimage X))
    (complexPowerKoszulTransition R a (DerivedCategory.Q.objPreimage X))
    X (completeDerivedKoszulHomotopyLimitIso R a X hX) i g N h x

end SerrePositivity.DerivedCompletion

end CompleteMilnorAnnihilatorPart

section PerfectResidueCompletedTensorPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "Ip" => Ideal.span {(p : R)}
local notation "Rq" => R ⧸ Ip
local notation "Sq" => S ⧸ Ideal.map (algebraMap R S) Ip
local notation "Tq" => T ⧸ Ideal.map (algebraMap R T) Ip

/-- The original module tensor completion is discrete with injective p action on H0. -/
lemma completedTensor_pure_of_perfect_residue
    [hRq : PerfectRing Rq p] [hSq : PerfectRing Sq p] [hTq : PerfectRing Tq p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    let X := (boundedAboveDerivedCompletionFunctor R (p : R)).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S),
          boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => (p : R) • x) := by
  let X0 := boundedAboveDerivedTensor.obj
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S),
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))
  let X := (boundedAboveDerivedCompletionFunctor R (p : R)).obj X0
  apply derived_pure_of_complete_regular_quotient_pure (p : R) ha X
    (derivedComplexCompletionFunctor_isComplete R (p : R) X0.obj)
  intro i hi
  have hSacyc := scalarExtensionTorVanishing_principal_of_regular (p : R) ha
    (ModuleCat.of R S) hS
  have hTacyc := scalarExtensionTorVanishing_principal_of_regular (p : R) ha
    (ModuleCat.of R T) hT
  let q := Ideal.Quotient.mk Ip
  let ec : (boundedAboveDerivedBaseChange q).obj X ≅
      (boundedAboveDerivedBaseChange q).obj X0 := by
    have e := (boundedAboveDerivedCompletionQuotientIso R (p : R) ha 1 X0).symm
    rw [pow_one] at e
    exact e
  let eq := derivedTensorQuotientAlgebraIso Ip S T hSacyc hTacyc
  have hpq : (p : Rq) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Ip)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have haug : IsIso (boundedAboveDerivedTensorAlgebraAugmentation (R := Rq) Sq Tq).hom.hom :=
    @perfectRing_derivedTensorAlgebraAugmentation_isIso_of_char_eq_zero p _ Rq _ hRq hpq
      Sq _ (adicQuotientAlgebra Ip S) hSq Tq _ (adicQuotientAlgebra Ip T) hTq
  have := haug
  let aug := (boundedAboveDerivedTensorAlgebraAugmentation (R := Rq) Sq Tq).hom.hom
  let ea := DerivedCategory.Minus.ι.mapIso (asIso aug)
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Rq) i).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Rq Sq),
          boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Rq Tq))).obj) := by
    exact (derivedSingleHomology_isZero (ModuleCat.of Rq (Sq ⊗[Rq] Tq)) i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat Rq) i).mapIso ea)
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Rq) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (ec ≪≫ eq)))

/-- The same purity applies to the original completed commutative algebra object. -/
lemma completedTensorAlgebra_pure_of_perfect_residue
    [PerfectRing Rq p] [PerfectRing Sq p] [PerfectRing Tq p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    let X := (boundedAboveCompletedTensorAlgebra R (p : R) S T).X
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => (p : R) • x) := by
  exact completedTensor_pure_of_perfect_residue p R S T ha hS hT

/-- Multiplication by p on the actual H0 ring is injective. -/
lemma completedTensorH0_p_mul_injective_of_perfect_residue
    [PerfectRing Rq p] [PerfectRing Sq p] [PerfectRing Tq p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    let := derivedH0CommRing A
    Function.Injective (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj =>
      (p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) * x) := by
  let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  have hreg := (completedTensorAlgebra_pure_of_perfect_residue p R S T ha hS hT).2.2
  change Function.Injective
    (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj =>
    (p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) * x)
  intro x y hxy
  apply hreg
  change (p : R) • x = (p : R) • y
  simpa only [Algebra.smul_def, map_natCast] using hxy

/-- The actual H0 ring is classically p-adically complete. -/
lemma completedTensorH0_isAdicComplete_of_perfect_residue
    [PerfectRing Rq p] [PerfectRing Sq p] [PerfectRing Tq p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    let := derivedH0CommRing A
    IsAdicComplete
      (Ideal.span {(p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)})
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) := by
  let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
  let H := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  have hc : IsComplete R (p : R) A.X.obj :=
    derivedComplexCompletionFunctor_isComplete R (p : R) _
  have hH := isComplete_homology_isModuleComplete R (p : R) A.X.obj hc 0
  have hreg := (completedTensorAlgebra_pure_of_perfect_residue p R S T ha hS hT).2.2
  have hAH : IsAdicComplete Ip H :=
    (isModuleComplete_iff_isAdicComplete_of_regular R (p : R) H hreg).mp hH
  change IsAdicComplete (Ideal.span {(p : H)}) H
  have hself :=
    (IsAdicComplete.map_algebraMap_iff (I := Ip) (S := H) (M := H)).mpr hAH
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hself
end SerrePositivity.DerivedCompletion

end PerfectResidueCompletedTensorPart
