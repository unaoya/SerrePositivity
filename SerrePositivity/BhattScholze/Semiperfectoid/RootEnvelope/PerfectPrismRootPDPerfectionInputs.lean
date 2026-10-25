module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.PerfectPrismRootPDCompletelyFlat
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaAlgebra.PerfectPrismDeltaAlgebraDiscrete
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion

/-! # 任意根族の実PD環から実δ完全化の離散性への具体的入力 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
section Coefficients
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (Functor.obj boundedAboveDerivedSingleFunctor (baseChangeScalarModule j))

/-- 実PD係数加群は、元の標準環射A→PDに沿う制限加群そのものである。 -/
def deltaRootPDSourceModuleIso :
    letI := pdCompletionCommRing Raw p z
    M ≅ baseChangeScalarModule j := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionAlgebra Raw p z
  let Mc : ModuleCat.{u} A := M
  let Nc : ModuleCat.{u} A := baseChangeScalarModule j
  let f : Mc →ₗ[A] Nc :=
    { toFun := (id : B → B)
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change B at x
        change (c a) • x = s (c a) * x
        exact Algebra.smul_def (c a) x }
  let g : Nc →ₗ[A] Mc :=
    { toFun := (id : B → B)
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change B at x
        change s (c a) * x = (c a) • x
        exact (Algebra.smul_def (c a) x).symm }
  let e : Mc ≃ₗ[A] Nc := LinearEquiv.ofLinearMap f g (by ext x; rfl) (by ext x; rfl)
  exact e.toModuleIso

/-- 同じ標準PD係数射は、元のδ構造からのδ射。 -/
theorem deltaRootPDSourceCoefficient_isDeltaHom :
    letI := pdCompletionCommRing Raw p z
    D.IsDeltaHom G j := by
  let := pdCompletionCommRing Raw p z
  exact (pdCompletionUnit_isDeltaHom F z).comp
    ((deltaAdjoinDivisionMap_isDeltaHom E (MvPolynomial.C d) r).comp
      (polynomialRankOneDeltaStructure_C_isDeltaHom σ D))

end Coefficients

section Perfect
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (Functor.obj boundedAboveDerivedSingleFunctor (baseChangeScalarModule j))

include hP

/-- 完全prism上では、同じPD係数射に沿う実還元の非零次数は消える。 -/
theorem perfectPrismRootPDSource_reduction_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := pdCompletionCommRing Raw p z
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  let := pdCompletionCommRing Raw p z
  have hz := perfectPrismRootPD_reduction_homology_isZero P hP b i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
      (boundedAboveDerivedSingleFunctor.mapIso (deltaRootPDSourceModuleIso D d b))))).symm

/-- 同じ標準PD係数射に沿う実還元のH0は忠実平坦。 -/
theorem perfectPrismRootPDSource_reductionH0_faithfullyFlat :
    letI := pdCompletionCommRing Raw p z
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let := pdCompletionCommRing Raw p z
  let : Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj) :=
    perfectPrismRootPD_reductionH0_faithfullyFlat P hP b
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
        (boundedAboveDerivedSingleFunctor.mapIso
          (deltaRootPDSourceModuleIso D d b))))).toLinearEquiv.symm

/-- 任意根族の実PD環のδ完全化を逐次実完備化した具体的対象は離散。 -/
theorem perfectPrismRootPDPerfectionCompletion_pure :
    letI := pdCompletionCommRing Raw p z
    let X := DeltaAlgebraPerfectionIteratedPDCompletion G j d
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 := by
  let := pdCompletionCommRing Raw p z
  exact perfectPrismDeltaAlgebraCompletion_pure P G j hP
    (deltaRootPDSourceCoefficient_isDeltaHom D d b)
    (perfectPrismRootPDSource_reduction_homology_isZero P hP b)
    (perfectPrismRootPDSource_reductionH0_faithfullyFlat P hP b)

/-- 同じ具体的δ完全化逐次対象の生成元冪商も離散でH0のp冪ねじれは有界。 -/
theorem perfectPrismRootPDPerfectionPower_pure_bounded_torsion (n : ℕ) (hn : 0 < n) :
    letI := pdCompletionCommRing Raw p z
    let X := DeltaAlgebraPerfectionIteratedPDCompletion G j d
    let T := A ⧸ Ideal.span {d ^ n}
    let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ k : ℕ,
        ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} T) 0).obj Z.obj,
          (p : T) ^ k • x = 0 → (p : T) ^ N • x = 0 := by
  let := pdCompletionCommRing Raw p z
  exact perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion P G j hP
    (deltaRootPDSourceCoefficient_isDeltaHom D d b)
    (perfectPrismRootPDSource_reduction_homology_isZero P hP b)
    (perfectPrismRootPDSource_reductionH0_faithfullyFlat P hP b) n hn

end Perfect
end SerrePositivity.BhattScholze
