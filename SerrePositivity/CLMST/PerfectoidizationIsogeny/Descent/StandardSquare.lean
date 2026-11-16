module

public import SerrePositivity.BhattScholze.Perfectoidization.Cone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Presentation
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Completion
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators
public import SerrePositivity.HomologicalAlgebra.CompletedFlatBoundedComparison
public import SerrePositivity.HomologicalAlgebra.AlgebraScalarExtensionModule
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensorComparison
public import SerrePositivity.HomologicalAlgebra.CompleteFaithfullyFlatDescent
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorVanishing
public import SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange
public import SerrePositivity.CommutativeAlgebra.TensorProduct.BaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure

/-! # 標準射の完備な基底変更の四角と錐の比較

## 概要

有限・有限表示な `S` の通常のテンソル積の導来完備性と、始域の完備な導来基底変更との同型（`sourceCompletedBaseChangeIso`）、通常のテンソル積の完備化と標準 perfectoid 化の四角（`completion_square`）、元の標準射の完備な基底変更の四角（`completedBaseChange_standard_square`）を与える。標準射の四角から錐全体の比較（`DerivedCompletion.completedModuleConeIso`）と全剰余段への比較（`standardReductionConeIso`）を作り、選んだ perfectoid 化とその錐の導来 p 完備性を示す。

## 方針

始域・終域・四角形を未知の仮定として受け取らず、証明済みの標準比較（BhattScholze/Perfectoidization/CompletedTensorComparison）を使う。錐は完全三角形の第三対象として比べる。

## 規約

CLMST Prop 2.4.7 の証明の標準の四角（原典の BS 8.13 による終域の比較を含む）。有界 p 冪ねじれは完備な基底変更の古典的な比較だけに使う。旧 `CLMST/Prop247StandardSquare`・`Prop247StandardCone`・`Prop247SourceComparison`・`Prop247ConeComparison`・`Prop247Cone`・`Prop247RankCompleteness`・`Prop247BaseChange`。`ConeComparison`・`Cone`・`RankCompleteness` の一般部分は 2b で HomologicalAlgebra/DerivedCompletion（`IntegralPerfectoid`・`CompletedTensorVanishing`）へ下ろした。

## 使われ方

`Descent/Uniform`、`Rank/*`。
-/

@[expose] public noncomputable section

universe u


section ConePart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

/-- 選択済み perfectoid 化は、元の R 作用について導来 p 完備。 -/
theorem target_isModuleComplete :
    IsModuleComplete R (p : R) (ModuleCat.of R (Perfectoidization R S p hR)) :=
  (isPerfectoidization_toPerfectoidization R S p hR).1.isModuleComplete_algebra
    R (Perfectoidization R S p hR) p

/-- Prop 2.4.7 の実際の標準写像の実導来錐は p 完備。
エタール性、J、g、André 拡大、almost 比較を使わない。 -/
theorem cone_isComplete :
    IsComplete R (p : R) (BhattScholze.perfectoidizationCone R S p hR) := by
  exact cone_isComplete_of_integralPerfectoid_target R S p hR
    (Perfectoidization R S p hR) (isPerfectoidization_toPerfectoidization R S p hR).1
    (BhattScholze.perfectoidizationModuleMap R S p hR)

end SerrePositivity.CLMST

end ConePart

section BaseChangePart

namespace SerrePositivity.CLMST
open _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false

variable (B L : Type u) [CommRing B] [CommRing L] [Algebra B L]
    [Module.FinitePresentation B L] (p : ℕ) [Fact p.Prime]

/-- 有限表示代数の古典 p 完備化への実標準射は全射。
分離性や bounded torsion をこの全射性に追加しない。 -/
theorem completion_unit_surjective (hB : IsIntegralPerfectoid B p) :
    Function.Surjective (algebraMap L (AdicCompletion (Ideal.span {(p : L)}) L)) := by
  have hL := isModuleComplete_of_finitePresentation B (p : B)
    (hB.isModuleComplete B p) (ModuleCat.of B L)
  have hL' : IsModuleComplete L (p : L) (ModuleCat.of L L) := by
    simpa only [map_natCast] using
      (isModuleComplete_algebraMap_iff B L (p : B) L).mpr hL
  let : IsPrecomplete (Ideal.span {(p : L)}) L :=
    isPrecomplete_of_adicRecurrenceMap_surjective (p : L)
      ((isModuleComplete_iff_recurrence_bijective L (p : L) _).mp hL').2
  exact AdicCompletion.of_surjective (Ideal.span {(p : L)}) L

omit [Module.FinitePresentation B L] in
/-- 原典の通常底変換 S⊗R B（係数環を左に置く）の実完備化標準射への適用。 -/
theorem tensor_completion_unit_surjective
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R B] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (hB : IsIntegralPerfectoid B p) :
    Function.Surjective (algebraMap (B ⊗[R] S)
      (AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S))) := by
  let := Module.FinitePresentation.of_finite_of_finitePresentation R S
  exact completion_unit_surjective B (B ⊗[R] S) p hB

variable {B L} {C : Type u} [CommRing C] [Algebra B C]

omit [Module.FinitePresentation B L] in
/-- 元の B 作用を保持した、指定 perfectoid 化写像の完備化への標準延長。 -/
def completionMap (β : L →ₐ[B] C) (hβ : IsPerfectoidization p β.toRingHom) :
    AdicCompletion (Ideal.span {(p : L)}) L →ₐ[B] C :=
  { IsPerfectoidization.completionMap p hβ with
    commutes' b := by
      have h := RingHom.congr_fun (IsPerfectoidization.completionMap_comp p hβ)
        (algebraMap B L b)
      exact h.trans (β.commutes b) }

omit [Module.FinitePresentation B L] in
/-- 標準延長の単位図式は、元の全ての元について可換。 -/
theorem completionMap_unit (β : L →ₐ[B] C)
    (hβ : IsPerfectoidization p β.toRingHom) (x : L) :
    completionMap p β hβ
      (algebraMap L (AdicCompletion (Ideal.span {(p : L)}) L) x) = β x :=
  RingHom.congr_fun (IsPerfectoidization.completionMap_comp p hβ) x

omit [Module.FinitePresentation B L] in
/-- 指定された終域同型（BS 8.13 の環版の出力を受け取る位置）を含む実四角形。
右下から右上への射は e、左下から左上への射は古典完備化の標準射。 -/
theorem completion_square {T : Type u} [CommRing T] [Algebra B T]
    (β : L →ₐ[B] C) (hβ : IsPerfectoidization p β.toRingHom) (e : C ≃ₐ[B] T) :
    (e.toAlgHom.comp (completionMap p β hβ)).comp
      (IsScalarTower.toAlgHom B L (AdicCompletion (Ideal.span {(p : L)}) L)) =
      e.toAlgHom.comp β := by
  ext x
  exact congrArg e (completionMap_unit p β hβ x)

/-- 標準完備化の実図式で、β の錐零化から α の錐零化へ移す。 -/
theorem completion_cone_bound
    (hB : IsIntegralPerfectoid B p) (β : L →ₐ[B] C)
    (hβ : IsPerfectoidization p β.toRingHom) (g : B) (q : ℕ)
    (hq : moduleMapConeScalar B β.toLinearMap (g ^ q) = 0) :
    moduleMapConeScalar B (completionMap p β hβ).toLinearMap (g ^ (2 * q)) = 0 := by
  apply moduleMapConeScalar_of_surjective_source
    (IsScalarTower.toAlgHom B L
      (AdicCompletion (Ideal.span {(p : L)}) L)).toLinearMap
    (completion_unit_surjective B L p hB)
    (completionMap p β hβ).toLinearMap β.toLinearMap _ g q hq
  ext x
  exact completionMap_unit p β hβ x

end SerrePositivity.CLMST

end BaseChangePart

section SourceComparisonPart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hB : IsIntegralPerfectoid B p)

include hB in
/-- 原典の通常 tensor は、有限表示により元の B 作用について導来 p 完備。 -/
theorem sourceTensor_isModuleComplete :
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
def sourceCompletedBaseChangeIso :
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
    simpa only [map_natCast] using sourceTensor_isModuleComplete R S B p hB
  exact completedBaseChangeBoundedAugmentationIso (algebraMap R B) (p : R)
    hflat (ModuleCat.of R S) N hM hL ≪≫
    (moduleObjectFunctor B).mapIso (algebraScalarExtensionModuleIso R B (ModuleCat.of R S))

/-- 始域比較は元の完備化単位と通常 tensor への標準 augmentation を保つ。 -/
theorem sourceCompletedBaseChangeIso_unit :
    (derivedComplexCompletionUnit B (algebraMap R B (p : R))).app
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj ≫
      (sourceCompletedBaseChangeIso R S B p hB hflat N hbounded).hom =
        (boundedAboveDerivedBaseChangeModuleAugmentation (algebraMap R B)).app (ModuleCat.of R S) ≫
          (moduleObjectFunctor B).map
            (algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom := by
  dsimp only [sourceCompletedBaseChangeIso]
  rw [Iso.trans_hom, ← Category.assoc, completedBaseChangeBoundedAugmentationIso_unit]
  rfl

include hB hflat N hbounded in
/-- 原典の通常 tensor は bounded torsion と完全平坦性の下で古典的にも p 完備。 -/
theorem sourceTensor_isAdicComplete :
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
    simpa only [map_natCast] using sourceTensor_isModuleComplete R S B p hB
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
def sourceCompletedAdicIso :
    (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B
        (AdicCompletion (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S))) := by
  let := sourceTensor_isAdicComplete R S B p hB hflat N hbounded
  exact sourceCompletedBaseChangeIso R S B p hB hflat N hbounded ≪≫
    (moduleObjectFunctor B).mapIso
      ((AdicCompletion.ofLinearEquiv
        (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S)).restrictScalars B).toModuleIso

/-- 古典完備化への始域比較でも、元の二つの標準単位を保つ。 -/
theorem sourceCompletedAdicIso_unit :
    (derivedComplexCompletionUnit B (algebraMap R B (p : R))).app
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj ≫
      (sourceCompletedAdicIso R S B p hB hflat N hbounded).hom =
        (boundedAboveDerivedBaseChangeModuleAugmentation (algebraMap R B)).app (ModuleCat.of R S) ≫
          (moduleObjectFunctor B).map
            (algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom ≫
          (moduleObjectFunctor B).map (ModuleCat.ofHom
            ((AdicCompletion.of (Ideal.span {(p : B ⊗[R] S)}) (B ⊗[R] S)).restrictScalars B)) := by
  dsimp only [sourceCompletedAdicIso]
  rw [Iso.trans_hom, ← Category.assoc, sourceCompletedBaseChangeIso_unit, Category.assoc]
  rfl

end SerrePositivity.CLMST

end SourceComparisonPart

section StandardSquarePart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S B C P : Type u) [CommRing R] [CommRing S] [CommRing B]
    [CommRing C] [CommRing P] [Algebra R S] [Algebra R B] [Algebra R C] [Algebra B P]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hB : IsIntegralPerfectoid B p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (β : B ⊗[R] S →ₐ[B] P) (hβ : IsPerfectoidization p β.toRingHom)
set_option quotPrecheck false in
local notation "XS" => ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
  (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj
set_option quotPrecheck false in
local notation "XC" => ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
  (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C))).obj
local notation "AC" => boundedAboveCompletedTensorAlgebra R (p : R) B C

/-- 元の射の底変換と完備化単位を、終域の実 H⁰ 比較で写すと元の β となる。 -/
theorem targetH0LinearEquiv_unit_map
    (x : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj XS) :
    BhattScholze.targetH0LinearEquiv R S B C P p hR hB f hf β hβ
      ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
        ((derivedComplexCompletionUnit B (algebraMap R B (p : R))).app XC)
        ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
          ((boundedAboveDerivedBaseChange (algebraMap R B)).map
            (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))).hom x)) =
    β ((algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom
      ((boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.app
        (ModuleCat.of R S) x)) := by
  let := derivedH0CommRing AC
  let := derivedH0Algebra AC
  let := completedTensorH0LeftAlgebra R (p : R) B C
  let m := ModuleCat.ofHom f.toLinearMap
  let u := ((boundedAboveDerivedBaseChange (algebraMap R B)).map
    (boundedAboveDerivedSingleFunctor.map m)).hom
  let e := BhattScholze.targetTensorAlgEquiv R S B C P p hR hB f hf β hβ
  change e (completedBaseChangeTensorH0LinearEquiv R B C (p : R)
    ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
      ((derivedComplexCompletionUnit B (algebraMap R B (p : R))).app XC)
      ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map u x))) = _
  rw [BhattScholze.completedBaseChangeTensorH0_unit]
  have hn := (boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.naturality m
  have hx : (boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.app
      (ModuleCat.of R C) ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map u x) =
    (ModuleCat.extendScalars (algebraMap R B)).map m
      ((boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.app (ModuleCat.of R S) x) :=
    congrArg (fun k => k.hom x) hn
  rw [hx, algebraScalarExtensionModuleIso_algMap_apply]
  exact RingHom.congr_fun (BhattScholze.targetTensorAlgEquiv_comp R S B C P p hR hB f hf β hβ) _

variable [Module.Finite R S] [Algebra.FinitePresentation R S]
    (hflat : IsCompletelyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B)))
    (N : ℕ) (hbounded : ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)

/-- 始域・終域の実比較は、元の射の完備導来底変換と元の β を結ぶ標準四角形をなす。 -/
theorem completedBaseChange_standard_square :
    (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).map
        ((boundedAboveDerivedBaseChange (algebraMap R B)).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))).hom ≫
      (BhattScholze.targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ).hom =
    (sourceCompletedBaseChangeIso R S B p hB hflat N hbounded).hom ≫
      (moduleObjectFunctor B).map (ModuleCat.ofHom β.toLinearMap) := by
  let φ := algebraMap R B
  let F := derivedComplexCompletionFunctor B (φ (p : R))
  let η := derivedComplexCompletionUnit B (φ (p : R))
  let u := ((boundedAboveDerivedBaseChange φ).map
    (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))).hom
  let eS := sourceCompletedBaseChangeIso R S B p hB hflat N hbounded
  let eC := BhattScholze.targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ
  let βM := ModuleCat.ofHom β.toLinearMap
  have hP : IsComplete B (φ (p : R)) ((moduleObjectFunctor B).obj (ModuleCat.of B P)) := by
    change IsModuleComplete B (φ (p : R)) (ModuleCat.of B P)
    simpa only [φ, map_natCast] using hβ.1.isModuleComplete_algebra B P p
  apply derivedComplexCompletionHom_ext B (φ (p : R)) hP
  change η.app XS ≫ (F.map u ≫ eC.hom) =
    η.app XS ≫ (eS.hom ≫ (moduleObjectFunctor B).map βM)
  rw [← Category.assoc, ← η.naturality u, Category.assoc]
  rw [← Category.assoc (η.app XS) eS.hom,
    sourceCompletedBaseChangeIso_unit]
  have : (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)).obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj _).IsLE 0
    infer_instance
  have : (XS).IsLE 0 := boundedAboveLeftDerived_isLE (ModuleCat.extendScalars φ)
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)) 0
  apply (derivedNonpositiveHomToSingleEquiv XS (ModuleCat.of B P)).injective
  simp only [derivedNonpositiveHomToSingleEquiv_apply, Functor.map_comp, Category.assoc]
  have hc := BhattScholze.targetCompletedBaseChangeIso_homology R S B C P p hR hB f hf β hβ
  change (DerivedCategory.homologyFunctor (ModuleCat B) 0).map eC.hom ≫ _ = _ at hc
  rw [hc]
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0
  have hnβ := ε.hom.naturality βM
  change (DerivedCategory.homologyFunctor (ModuleCat B) 0).map
      ((moduleObjectFunctor B).map βM) ≫ ε.hom.app (ModuleCat.of B P) =
    ε.hom.app (ModuleCat.of B (B ⊗[R] S)) ≫ βM at hnβ
  rw [hnβ]
  have hn := ε.hom.naturality (algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom
  change (DerivedCategory.homologyFunctor (ModuleCat B) 0).map
      ((moduleObjectFunctor B).map (algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom) ≫
      ε.hom.app (ModuleCat.of B (B ⊗[R] S)) =
    ε.hom.app ((ModuleCat.extendScalars φ).obj (ModuleCat.of R S)) ≫
      (algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom at hn
  erw [reassoc_of% hn]
  have hb := boundedAboveDerivedBaseChangeModuleAugmentation_homology φ (ModuleCat.of R S)
  rw [realizedSingleH0Iso_hom_eq_standard] at hb
  erw [reassoc_of% hb]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact targetH0LinearEquiv_unit_map R S B C P p hR hB f hf β hβ x

/-- 原典の古典完備化からの α を用いた、元の射の実標準四角形。 -/
theorem completedBaseChange_adic_standard_square :
    (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).map
        ((boundedAboveDerivedBaseChange (algebraMap R B)).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))).hom ≫
      (BhattScholze.targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ).hom =
    (sourceCompletedAdicIso R S B p hB hflat N hbounded).hom ≫
      (moduleObjectFunctor B).map
        (ModuleCat.ofHom (completionMap p β hβ).toLinearMap) := by
  rw [completedBaseChange_standard_square R S B C P p hR hB f hf β hβ hflat N hbounded]
  dsimp only [sourceCompletedAdicIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp]
  congr 1
  apply congrArg (moduleObjectFunctor B).map
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (completionMap_unit p β hβ x).symm

end SerrePositivity.CLMST

end StandardSquarePart


section StandardConePart

namespace SerrePositivity.CLMST
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S B C P : Type u) [CommRing R] [CommRing S] [CommRing B]
    [CommRing C] [CommRing P] [Algebra R S] [Algebra R B] [Algebra R C] [Algebra B P]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hB : IsIntegralPerfectoid B p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (β : B ⊗[R] S →ₐ[B] P) (hβ : IsPerfectoidization p β.toRingHom)
    (hflat : IsCompletelyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B)))
    (N : ℕ) (hbounded : ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)

/-- 元の射の実完備底変換錐は、原典の α の実加群錐と同型。 -/
def standardCompletedConeIso :
    (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (moduleMapConeBoundedAbove f.toLinearMap)).obj ≅
      moduleMapCone B (completionMap p β hβ).toLinearMap :=
  DerivedCompletion.completedModuleConeIso (algebraMap R B) (p : R) f.toLinearMap
    (completionMap p β hβ).toLinearMap
    (sourceCompletedAdicIso R S B p hB hflat N hbounded)
    (BhattScholze.targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ)
    (completedBaseChange_adic_standard_square R S B C P p hR hB f hf β hβ
      hflat N hbounded)

/-- 実錐の比較は元の三角形の標準の右包含を保つ。 -/
theorem standardCompletedConeIso_inclusion :
    (DerivedCompletion.completedModuleTriangle (algebraMap R B) (p : R) f.toLinearMap).mor₂ ≫
      (standardCompletedConeIso R S B C P p hR hB f hf β hβ hflat N hbounded).hom =
    (BhattScholze.targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ).hom ≫
      (moduleMapConeTriangle B (completionMap p β hβ).toLinearMap).mor₂ :=
  DerivedCompletion.completedModuleConeIso_inclusion (algebraMap R B) (p : R) f.toLinearMap
    (completionMap p β hβ).toLinearMap
    (sourceCompletedAdicIso R S B p hB hflat N hbounded)
    (BhattScholze.targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ)
    (completedBaseChange_adic_standard_square R S B C P p hR hB f hf β hβ
      hflat N hbounded)

/-- 全ての冪剰余段の実底変換を、原典の α の実錐の冪剰余へ比較する。 -/
def standardReductionConeIso (n : ℕ) :
    ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
      ((boundedAboveDerivedScalarCone R ((p : R) ^ n)).obj
        (moduleMapConeBoundedAbove f.toLinearMap))).obj ≅
    (derivedScalarConeFunctor B ((p : B) ^ n)).obj
      (moduleMapCone B (completionMap p β hβ).toLinearMap) := by
  have e := boundedAboveDerivedBaseChangePowerConeCompletionIso (algebraMap R B) (p : R) n
    (moduleMapConeBoundedAbove f.toLinearMap)
  rw [map_natCast] at e
  have c := standardCompletedConeIso R S B C P p hR hB f hf β hβ hflat N hbounded
  rw [map_natCast] at c
  exact e ≪≫ (derivedScalarConeFunctor B ((p : B) ^ n)).mapIso c

end SerrePositivity.CLMST

end StandardConePart

