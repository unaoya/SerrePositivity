module

public import SerrePositivity.CLMST.Prop247BaseChange
public import SerrePositivity.HomologicalAlgebra.CompletedFlatBoundedComparison
public import SerrePositivity.HomologicalAlgebra.AlgebraScalarExtensionModule
public import SerrePositivity.CommutativeAlgebra.Adic.Complete

/-! # Prop 2.4.7：始域の完備導来底変換と通常 tensor

有限かつ有限表示な元の S の仮定から通常 tensor の導来完備性を証明する。
元の bounded torsion 仮定と完全平坦性を使い、標準 augmentation の完備化を同型にする。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hB : IsIntegralPerfectoid B p)

include hB in
/-- 原典の通常 tensor は、有限表示により元の B 作用について導来 p 完備。 -/
theorem prop247_sourceTensor_isModuleComplete :
    IsModuleComplete B (p : B)
      ((ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R S)) := by
  let := Module.FinitePresentation.of_finite_of_finitePresentation R S
  apply isComplete_of_iso B (p : B)
    ((moduleObjectFunctor B).mapIso (algebraScalarExtensionModuleIso R B (ModuleCat.of R S))).symm
  exact isModuleComplete_of_finitePresentation B (p : B) (hB.isModuleComplete B p) _

variable (hflat : IsCompletelyFlat (Ideal.span {(p : R)})
    (baseChangeScalarModule (algebraMap R B)))
    (N : ℕ) (hbounded : ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)

/-- 元の始域の完備導来底変換から通常 tensor への実標準比較。 -/
def prop247_sourceCompletedBaseChangeIso :
    (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B (B ⊗[R] S)) := by
  have hM : ∀ n : ℕ, ∀ s : ModuleCat.of R S,
      (p : R) ^ n • s = 0 → (p : R) ^ N • s = 0 := by
    intro n s hs
    change (p : R) ^ n • (s : S) = 0 at hs
    have hs' : (p : S) ^ n * s = 0 := by
      simpa only [Algebra.smul_def, map_pow, map_natCast] using hs
    change (p : R) ^ N • (s : S) = 0
    simpa only [Algebra.smul_def, map_pow, map_natCast] using hbounded n s hs'
  have hL : IsModuleComplete B (algebraMap R B (p : R))
      ((ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R S)) := by
    simpa only [map_natCast] using prop247_sourceTensor_isModuleComplete R S B p hB
  exact completedBaseChangeBoundedAugmentationIso (algebraMap R B) (p : R)
    hflat (ModuleCat.of R S) N hM hL ≪≫
    (moduleObjectFunctor B).mapIso (algebraScalarExtensionModuleIso R B (ModuleCat.of R S))

/-- 始域比較は元の完備化単位と通常 tensor への標準 augmentation を保つ。 -/
theorem prop247_sourceCompletedBaseChangeIso_unit :
    (derivedComplexCompletionUnit B (algebraMap R B (p : R))).app
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj ≫
      (prop247_sourceCompletedBaseChangeIso R S B p hB hflat N hbounded).hom =
        (boundedAboveDerivedBaseChangeModuleAugmentation (algebraMap R B)).app (ModuleCat.of R S) ≫
          (moduleObjectFunctor B).map
            (algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom := by
  dsimp only [prop247_sourceCompletedBaseChangeIso]
  rw [Iso.trans_hom, ← Category.assoc, completedBaseChangeBoundedAugmentationIso_unit]
  rfl

include hB hflat N hbounded in
/-- 原典の通常 tensor は bounded torsion と完全平坦性の下で古典的にも p 完備。 -/
theorem prop247_sourceTensor_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S) := by
  have hM : ∀ n : ℕ, ∀ s : ModuleCat.of R S,
      (p : R) ^ n • s = 0 → (p : R) ^ N • s = 0 := by
    intro n s hs
    change (p : R) ^ n • (s : S) = 0 at hs
    have hs' : (p : S) ^ n * s = 0 := by
      simpa only [Algebra.smul_def, map_pow, map_natCast] using hs
    change (p : R) ^ N • (s : S) = 0
    simpa only [Algebra.smul_def, map_pow, map_natCast] using hbounded n s hs'
  have hL : IsModuleComplete B (algebraMap R B (p : R))
      ((ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R S)) := by
    simpa only [map_natCast] using prop247_sourceTensor_isModuleComplete R S B p hB
  have hc := isAdicComplete_extendScalars_of_bounded_torsion (algebraMap R B) (p : R)
    hflat (ModuleCat.of R S) N hM hL
  have hc' : IsAdicComplete (Ideal.span {(p : B)}) (B ⊗[R] S) := by
    have hc0 : IsAdicComplete (Ideal.span {(p : B)})
        ((ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R S)) := by
      simpa only [map_natCast] using hc
    exact isAdicComplete_of_linearEquiv _
      (algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).toLinearEquiv hc0
  have hm : IsAdicComplete
      ((Ideal.span {(p : B)}).map (algebraMap B (B ⊗[R] S))) (B ⊗[R] S) :=
    (IsAdicComplete.map_algebraMap_iff (Ideal.span {(p : B)}) (B ⊗[R] S)).mpr hc'
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hm

/-- 原典の始域を通常 tensor の古典 p 完備化へ同定する実比較。 -/
def prop247_sourceCompletedAdicIso :
    (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B
        (AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S))) := by
  let := prop247_sourceTensor_isAdicComplete R S B p hB hflat N hbounded
  exact prop247_sourceCompletedBaseChangeIso R S B p hB hflat N hbounded ≪≫
    (moduleObjectFunctor B).mapIso
      ((AdicCompletion.ofLinearEquiv
        (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S)).restrictScalars B).toModuleIso

/-- 古典完備化への始域比較でも、元の二つの標準単位を保つ。 -/
theorem prop247_sourceCompletedAdicIso_unit :
    (derivedComplexCompletionUnit B (algebraMap R B (p : R))).app
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj ≫
      (prop247_sourceCompletedAdicIso R S B p hB hflat N hbounded).hom =
        (boundedAboveDerivedBaseChangeModuleAugmentation (algebraMap R B)).app (ModuleCat.of R S) ≫
          (moduleObjectFunctor B).map
            (algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom ≫
          (moduleObjectFunctor B).map (ModuleCat.ofHom
            ((AdicCompletion.of (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S)).restrictScalars B)) := by
  dsimp only [prop247_sourceCompletedAdicIso]
  rw [Iso.trans_hom, ← Category.assoc, prop247_sourceCompletedBaseChangeIso_unit, Category.assoc]
  rfl

end SerrePositivity.CLMST
