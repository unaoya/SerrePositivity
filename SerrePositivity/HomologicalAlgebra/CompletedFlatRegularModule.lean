module

public import SerrePositivity.HomologicalAlgebra.ScalarConeModuleQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange
public import SerrePositivity.HomologicalAlgebra.PowerTorsionDerivedDescent
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity

/-! # 完全平坦な底変換と正則加群の完備導来 tensor

正則性は元の加群上にだけ要求する。環での正則性、有限性、元の加群の完備性は不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R)

/-- 完全平坦性により、冪で消える任意加群の高次 Tor が消える。 -/
theorem scalarExtensionTorVanishing_of_power_torsion
    (hB : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (M : ModuleCat.{u} R) (N : ℕ) (hM : ∀ x : M, a ^ N • x = 0) :
    scalarExtensionTorVanishing φ M := by
  intro i hi
  have : Subsingleton (((Tor (ModuleCat R) i).obj (baseChangeScalarModule φ)).obj M) :=
    torModule_subsingleton_of_completelyFlat_powerTorsion a (baseChangeScalarModule φ)
      hB N M hM i hi
  exact ModuleCat.isZero_of_subsingleton _

/-- 通常の係数拡大は、与えられた冪による零化を保つ。 -/
theorem extendScalars_pow_smul_zero (M : ModuleCat.{u} R) (N : ℕ)
    (hM : ∀ x : M, a ^ N • x = 0) :
    ∀ x : (ModuleCat.extendScalars φ).obj M, (φ a) ^ N • x = 0 := by
  have hz : a ^ N • 𝟙 M = 0 := by
    ext x
    exact hM x
  have he := congrArg (ModuleCat.extendScalars φ).map hz
  rw [extendScalars_scalar_id, Functor.map_zero, map_pow] at he
  intro x
  exact congrArg (fun f => f.hom x) he

/-- 冪で消える加群の完備導来底変換は、元の通常 tensor の single 対象と同型。
同型は導来底変換の標準 augmentation と完備化の標準単位から構成する。 -/
def completedBaseChangePowerTorsionIso
    (hB : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (M : ModuleCat.{u} R) (N : ℕ) (hM : ∀ x : M, a ^ N • x = 0) :
    (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj M)).obj ≅
        (moduleObjectFunctor B).obj ((ModuleCat.extendScalars φ).obj M) := by
  let e := DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedBaseChangeModuleAugmentationIso
    φ M (scalarExtensionTorVanishing_of_power_torsion φ a hB M N hM))
  exact (derivedComplexCompletionFunctor B (φ a)).mapIso e ≪≫
    (derivedComplexCompletionUnitIso B (φ a) _
      (isModuleComplete_of_pow_smul_zero B (φ a) _ N
        (extendScalars_pow_smul_zero φ a M N hM))).symm

/-- 冪 torsion の比較は元の標準 augmentation を保つ。 -/
theorem completedBaseChangePowerTorsionIso_unit
    (hB : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (M : ModuleCat.{u} R) (N : ℕ) (hM : ∀ x : M, a ^ N • x = 0) :
    (derivedComplexCompletionUnit B (φ a)).app
        ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj M)).obj ≫
      (completedBaseChangePowerTorsionIso φ a hB M N hM).hom =
        (boundedAboveDerivedBaseChangeModuleAugmentation φ).app M := by
  let e := DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedBaseChangeModuleAugmentationIso
    φ M (scalarExtensionTorVanishing_of_power_torsion φ a hB M N hM))
  change _ ≫ ((derivedComplexCompletionFunctor B (φ a)).map e.hom ≫ _) = e.hom
  rw [← Category.assoc]
  erw [← (derivedComplexCompletionUnit B (φ a)).naturality e.hom]
  let u := derivedComplexCompletionUnitIso B (φ a)
    ((moduleObjectFunctor B).obj ((ModuleCat.extendScalars φ).obj M))
    (isModuleComplete_of_pow_smul_zero B (φ a) _ N
      (extendScalars_pow_smul_zero φ a M N hM))
  change (e.hom ≫ u.hom) ≫ u.inv = e.hom
  simp

/-- 正則加群の完備導来底変換は離散で、その H⁰ でも元の像は正則である。 -/
theorem completedBaseChange_regular_module_pure
    (hB : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (M : ModuleCat.{u} R) (hM : IsSMulRegular M a) :
    let Y := (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    Y.IsGE 0 ∧ Y.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj Y => φ a • x) := by
  let X := boundedAboveDerivedSingleFunctor.obj M
  let Q := modulePowerReduction a M 1
  let eQ : (boundedAboveDerivedScalarCone R a).obj X ≅
      boundedAboveDerivedSingleFunctor.obj Q := ObjectProperty.isoMk _ (by
    change (derivedScalarConeFunctor R a).obj ((moduleObjectFunctor R).obj M) ≅
      (moduleObjectFunctor R).obj (modulePowerReduction a M 1)
    simpa only [pow_one] using derivedScalarConeModuleQuotientIso a M hM 1)
  let ht := scalarExtensionTorVanishing_of_power_torsion φ a hB Q 1
    (modulePowerReduction_pow_smul_zero a M 1)
  let eBC := DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange φ).mapIso eQ) ≪≫
    DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedBaseChangeModuleAugmentationIso φ Q ht)
  let Y := (derivedComplexCompletionFunctor B (φ a)).obj
    ((boundedAboveDerivedBaseChange φ).obj X).obj
  let ec : ((boundedAboveDerivedBaseChange φ).obj
      ((boundedAboveDerivedScalarCone R a).obj X)).obj ≅
      (derivedScalarConeFunctor B (φ a)).obj Y := by
    simpa only [pow_one] using boundedAboveDerivedBaseChangePowerConeCompletionIso φ a 1 X
  apply derived_pure_of_complete_scalarCone_pure (φ a) Y
    (derivedComplexCompletionFunctor_isComplete B (φ a) _)
  intro i hi
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars φ).obj Q) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat B) i).mapIso (ec.symm ≪≫ eBC))

end SerrePositivity
