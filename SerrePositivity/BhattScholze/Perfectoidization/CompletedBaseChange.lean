module

public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.RingEquivDerivedTensor
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.PowerTorsionCompletedBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChange
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs

/-!
# perfectoid 化の完備底変換

## 概要
perfectoid 係数の完備スカラー拡大の離散性、新しい底での係数の比較、完備底変換後の perfectoid 化の係数。

## 方針
完備テンソル積の離散性を底変換に適用する。

## 規約
—

## 使われ方
BS 著者版 Proposition 8.13 の環版。
-/

universe u

/-! ## The actual completed scalar extension of perfectoid coefficients is discrete

The target scalar ring is retained throughout restriction, completion, and the
normalized comparison with the actual zeroth homology module.
-/

@[expose] public noncomputable section PerfectoidCompletedBaseChangeDiscrete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory MonoidalCategory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R S C : Type u)
    [CommRing R] [CommRing S] [CommRing C] [Algebra R S] [Algebra R C]

/-- Complete the original actual scalar extension over S; its discreteness
follows from the original perfectoid tensor over R after restriction. -/
lemma integralPerfectoid_completedBaseChange_pure
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hC : IsIntegralPerfectoid C p) :
    let X := (boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 := by
  let φ := algebraMap R S
  let M := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)
  let X := (boundedAboveDerivedBaseChange φ).obj M
  let eS : derivedBaseChangeScalarObject φ ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S) :=
    boundedAboveDerivedSingleFunctor.mapIso (algebraSelfRestrictionIso R S)
  let B := boundedAboveCompletedTensorAlgebra R (p : R) S C
  let Y := (boundedAboveDerivedCompletionFunctor S (p : S)).obj X
  let e0 := ((boundedAboveCompletionRestrictionIso φ (p : R)).app X).symm ≪≫
    (boundedAboveDerivedCompletionFunctor R (p : R)).mapIso
      (boundedAboveDerivedBaseChangeTensorIso φ M ≪≫
        boundedAboveDerivedTensor.mapIso (Iso.prod eS (Iso.refl M)))
  have hpure := integralPerfectoid_completedTensor_pure p R S C hR hS hC
  letI : B.X.obj.IsGE 0 := hpure.1
  letI : B.X.obj.IsLE 0 := hpure.2
  let e : (derivedRestrictScalars φ).obj Y.obj ≅ B.X.obj := by
    have he := DerivedCategory.Minus.ι.mapIso e0
    change (derivedRestrictScalars φ).obj
        ((derivedComplexCompletionFunctor S (φ (p : R))).obj X.obj) ≅
      (derivedComplexCompletionFunctor R (p : R)).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S), M)).obj at he
    change (derivedRestrictScalars φ).obj
        ((derivedComplexCompletionFunctor S (p : S)).obj X.obj) ≅
      (derivedComplexCompletionFunctor R (p : R)).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S), M)).obj
    rw [map_natCast] at he
    exact he
  have hlo := DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  have hhi := DerivedCategory.TStructure.t.isLE_of_iso e.symm 0
  exact ⟨(derivedRestrictScalars_isGE_iff φ Y.obj 0).mp hlo,
    (derivedRestrictScalars_isLE_iff φ Y.obj 0).mp hhi⟩

/-- The S-linear comparison is normalized by the identity on the actual H⁰ module. -/
def integralPerfectoid_completedBaseChangeSingleIso
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hC : IsIntegralPerfectoid C p) :
    let X := (boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))
    X ≅ boundedAboveDerivedSingleFunctor.obj
      ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj X.obj) := by
  dsimp only
  have h := integralPerfectoid_completedBaseChange_pure p R S C hR hS hC
  letI := h.1
  letI := h.2
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso _ 0)

/-- Original Tor coefficient actions are detected by ordinary Tor over the new base,
using the actual H⁰ of the completed coefficient extension. -/
lemma integralPerfectoid_torCoefficientScalar_eq_zero_iff_completedBaseChangeTor
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hC : IsIntegralPerfectoid C p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R S)))
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (i : ℕ) (s : R) :
    let X := (boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))
    let M := (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj X.obj
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
      ∀ x : (((Tor (ModuleCat S) i).obj M).obj ((ModuleCat.extendScalars
        (algebraMap R S)).obj N)), algebraMap R S s • x = 0 := by
  let X := (boundedAboveDerivedCompletionFunctor S (p : S)).obj
    ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))
  let M := (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj X.obj
  let L := (ModuleCat.extendScalars (algebraMap R S)).obj N
  have ht : torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) (-(i : ℤ))).obj
        (X ⊗ boundedAboveDerivedSingleFunctor.obj L).obj, algebraMap R S s • x = 0 := by
    have h := torCoefficientScalar_eq_zero_iff_completed_baseChange_tensor_annihilated
      (C := C) (algebraMap R S) (p : R) hflat N k hN i s
    rw [map_natCast] at h
    exact h
  let eX := integralPerfectoid_completedBaseChangeSingleIso p R S C hR hS hC
  let e := (DerivedCategory.homologyFunctor (ModuleCat S) (-(i : ℤ))).mapIso
      (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensor.mapIso
        (Iso.prod eX (Iso.refl (boundedAboveDerivedSingleFunctor.obj L))))) ≪≫
    (boundedAboveDerivedTensorModuleTorNatIso M i).app L
  apply ht.trans
  constructor
  · intro h z
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective z
    rw [← e.toLinearEquiv.map_smul, h x, e.toLinearEquiv.map_zero]
  · intro h x
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.map_smul, h (e.toLinearEquiv x), e.toLinearEquiv.map_zero]

end SerrePositivity.BhattScholze

end PerfectoidCompletedBaseChangeDiscrete

/-! ## New-base coefficient comparison with a specified universal perfectoidization -/

@[expose] public noncomputable section CompletedBaseChangeCoefficientComparison

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "A" => boundedAboveDerivedTensorAlgebra (R := R) S T
local notation "AC" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AC).X.obj

/-- The original universal map restricts to precisely the original left factor algebra map. -/
lemma completedTensorPerfectoidizationMap_left (s : S) :
    letI := derivedH0CommRing AC
    letI := derivedH0Algebra AC
    completedTensorPerfectoidizationMap R p S T (s ⊗ₜ[R] (1 : T)) =
      completedTensorH0LeftAlgHom R (p : R) S T s := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  let c : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
      (ModuleCat.of R S) s
  have hfac : derivedTensorH0AlgEquiv S T
      (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c) =
      s ⊗ₜ[R] (1 : T) := by
    change derivedTensorH0AlgHom S T
      (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c) = _
    rw [derivedTensorH0AlgHom_left]
    change (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R S) ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat R) 0).inv.app (ModuleCat.of R S) s)) = _
    rw [show (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R S) ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat R) 0).inv.app (ModuleCat.of R S) s) = s from
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
        (ModuleCat.of R S)).toLinearEquiv.apply_symm_apply s]
    rfl
  have he : (derivedTensorH0AlgEquiv S T).symm (s ⊗ₜ[R] (1 : T)) =
      derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c := by
    apply (derivedTensorH0AlgEquiv S T).injective
    rw [AlgEquiv.apply_symm_apply, hfac]
  rw [completedTensorPerfectoidizationMap_apply, completedTensorH0LeftAlgHom_apply,
    he, derivedH0AlgMap_comp_apply]
  rfl

variable [Fact p.Prime]

/-- Universal comparison is linear over the new base with its original specified algebra action. -/
lemma completedTensorPerfectoidizationMap_exists_algEquiv
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p)
    (D : Type u) [CommRing D] [Algebra S D] (f : S ⊗[R] T →ₐ[S] D)
    (hf : IsPerfectoidization p f.toRingHom) :
    letI := derivedH0CommRing AC
    letI := derivedH0Algebra AC
    letI := completedTensorH0LeftAlgebra R (p : R) S T
    ∃ e : H ≃ₐ[S] D,
      e.toRingHom.comp (completedTensorPerfectoidizationMap R p S T) = f.toRingHom := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) S T
  obtain ⟨e, he⟩ := completedTensorPerfectoidizationMap_exists_equiv R p S T
    hR hS hT D f.toRingHom hf
  have hc (s : S) : e (algebraMap S H s) = algebraMap S D s := by
    change e (completedTensorH0LeftAlgHom R (p : R) S T s) = _
    rw [← completedTensorPerfectoidizationMap_left]
    exact (RingHom.congr_fun he (s ⊗ₜ[R] (1 : T))).trans (f.commutes s)
  exact ⟨AlgEquiv.ofRingEquiv (f := e) hc, he⟩

/-- The original S-completed base-change coefficient is S-linearly equivalent to any
specified universal perfectoidization of the ordinary tensor. -/
lemma completedBaseChangeH0_exists_linearEquiv_perfectoidization
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p)
    (D : Type u) [CommRing D] [Algebra S D] (f : S ⊗[R] T →ₐ[S] D)
    (hf : IsPerfectoidization p f.toRingHom) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (algebraMap R S (p : R))).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj ≃ₗ[S] D) := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) S T
  obtain ⟨e, _he⟩ := completedTensorPerfectoidizationMap_exists_algEquiv R p S T
    hR hS hT D f hf
  exact ⟨(completedBaseChangeTensorH0LinearEquiv R S T (p : R)).trans e.toLinearEquiv⟩

/-- Original coefficient actions can be tested on ordinary new-base Tor with the
specified perfectoidization coefficient, retaining all power-torsion test modules. -/
lemma integralPerfectoid_torCoefficientScalar_eq_zero_iff_selectedPerfectoidizationTor
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R S)))
    (D : Type u) [CommRing D] [Algebra S D] (f : S ⊗[R] T →ₐ[S] D)
    (hf : IsPerfectoidization p f.toRingHom)
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (i : ℕ) (s : R) :
    torCoefficientScalarEndomorphism T N i (algebraMap R T s) = 0 ↔
      ∀ x : (((Tor (ModuleCat S) i).obj (ModuleCat.of S D)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj N)), algebraMap R S s • x = 0 := by
  obtain ⟨eh⟩ := completedBaseChangeH0_exists_linearEquiv_perfectoidization R p S T
    hR hS hT D f hf
  rw [map_natCast] at eh
  let M := (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
    ((boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj
  let L := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let eM : M ≅ ModuleCat.of S D := eh.toModuleIso
  let e := ((Tor (ModuleCat S) i).mapIso eM).app L
  apply (integralPerfectoid_torCoefficientScalar_eq_zero_iff_completedBaseChangeTor
    p R S T hR hS hT hflat N k hN i s).trans
  constructor
  · intro h z
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective z
    rw [← e.toLinearEquiv.map_smul, h, map_zero]
  · intro h x
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.map_smul, h, map_zero]

end SerrePositivity.BhattScholze

end CompletedBaseChangeCoefficientComparison

/-! ## Original perfectoidization coefficients after completed base change -/

@[expose] public noncomputable section PerfectoidizationCompletedBaseChange

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (S A C : Type u)
    [CommRing S] [CommRing A] [CommRing C] [Algebra R S] [Algebra R A] [Algebra R C]
local notation "AC" => boundedAboveCompletedTensorAlgebra R (p : R) S C
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AC).X.obj

/-- The ordinary base change of the original perfectoidization map, followed by
the actual completed tensor unit, retaining the new base as the left factor. -/
def perfectoidizationCompletedBaseChangeMap (f : A →ₐ[R] C) :
    letI := derivedH0CommRing AC
    S ⊗[R] A →+* H := by
  letI := derivedH0CommRing AC
  exact (completedTensorPerfectoidizationMap R p S C).comp
    (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom

lemma perfectoidizationCompletedBaseChangeMap_left (f : A →ₐ[R] C) (s : S) :
    letI := derivedH0CommRing AC
    letI := derivedH0Algebra AC
    perfectoidizationCompletedBaseChangeMap R p S A C f (s ⊗ₜ[R] (1 : A)) =
      completedTensorH0LeftAlgHom R (p : R) S C s := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  change completedTensorPerfectoidizationMap R p S C (s ⊗ₜ[R] f 1) = _
  rw [map_one, completedTensorPerfectoidizationMap_left]

variable [Fact p.Prime]

/-- The same original base-change map is a universal perfectoidization. -/
lemma perfectoidizationCompletedBaseChangeMap_isPerfectoidization
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    letI := derivedH0CommRing AC
    IsPerfectoidization p (perfectoidizationCompletedBaseChangeMap R p S A C f) := by
  letI := derivedH0CommRing AC
  have hF := (completedTensorPerfectoidizationMap_isPerfectoidization
    R p S C hR hS hf.1).precomp_ringEquiv (Algebra.TensorProduct.comm R C S).toRingEquiv
  have hG := (perfectoidizationTensorBaseChangeMap_isPerfectoidization p f hf _ hF).precomp_ringEquiv
    (Algebra.TensorProduct.comm R S A).toRingEquiv
  convert hG using 1
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Comparison with the perfectoidization of the original base-changed algebra
preserves the new base action and the original base-changed unit. -/
lemma perfectoidizationCompletedBaseChangeMap_exists_algEquiv
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (D : Type u) [CommRing D] [Algebra S D] (g : S ⊗[R] A →ₐ[S] D)
    (hg : IsPerfectoidization p g.toRingHom) :
    letI := derivedH0CommRing AC
    letI := derivedH0Algebra AC
    letI := completedTensorH0LeftAlgebra R (p : R) S C
    ∃ e : H ≃ₐ[S] D,
      e.toRingHom.comp (perfectoidizationCompletedBaseChangeMap R p S A C f) =
        g.toRingHom := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) S C
  obtain ⟨e, he⟩ := (perfectoidizationCompletedBaseChangeMap_isPerfectoidization
    R p S A C hR hS f hf).exists_equiv p hg
  have hc (s : S) : e (algebraMap S H s) = algebraMap S D s := by
    change e (completedTensorH0LeftAlgHom R (p : R) S C s) = _
    rw [← perfectoidizationCompletedBaseChangeMap_left R p S A C f s]
    exact (RingHom.congr_fun he (s ⊗ₜ[R] (1 : A))).trans (g.commutes s)
  exact ⟨AlgEquiv.ofRingEquiv (f := e) hc, he⟩

/-- Original completed scalar extension of C has the original new-base module of
any specified perfectoidization of the base change of A. -/
lemma perfectoidizationCompletedBaseChange_exists_linearEquiv
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (D : Type u) [CommRing D] [Algebra S D] (g : S ⊗[R] A →ₐ[S] D)
    (hg : IsPerfectoidization p g.toRingHom) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (p : S)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))).obj ≃ₗ[S] D) := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) S C
  obtain ⟨e, _he⟩ := perfectoidizationCompletedBaseChangeMap_exists_algEquiv
    R p S A C hR hS f hf D g hg
  have eH := completedBaseChangeTensorH0LinearEquiv R S C (p : R)
  rw [map_natCast] at eH
  exact ⟨eH.trans e.toLinearEquiv⟩

/-- Original C-coefficient Tor is detected by the specified perfectoidization of
the base-changed original algebra A, with the original new-base scalar action. -/
lemma perfectoidization_torCoefficientScalar_eq_zero_iff_baseChangedPerfectoidizationTor
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R S)))
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (D : Type u) [CommRing D] [Algebra S D] (g : S ⊗[R] A →ₐ[S] D)
    (hg : IsPerfectoidization p g.toRingHom)
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (i : ℕ) (s : R) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
      ∀ x : (((Tor (ModuleCat S) i).obj (ModuleCat.of S D)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj N)), algebraMap R S s • x = 0 := by
  obtain ⟨eh⟩ := perfectoidizationCompletedBaseChange_exists_linearEquiv
    R p S A C hR hS f hf D g hg
  let M := (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
    ((boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))).obj
  let L := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let eM : M ≅ ModuleCat.of S D := eh.toModuleIso
  let e := ((Tor (ModuleCat S) i).mapIso eM).app L
  apply (integralPerfectoid_torCoefficientScalar_eq_zero_iff_completedBaseChangeTor
    p R S C hR hS hf.1 hflat N k hN i s).trans
  constructor
  · intro h z
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective z
    rw [← e.toLinearEquiv.map_smul, h, map_zero]
  · intro h x
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.map_smul, h, map_zero]

end SerrePositivity.BhattScholze

end PerfectoidizationCompletedBaseChange
