module

public import SerrePositivity.CLMST.Prop247SourceComparison
public import SerrePositivity.CLMST.Prop247TargetComparison
public import SerrePositivity.CLMST.Prop247TensorUnit

/-! # Prop 2.4.7：元の標準射の実完備底変換四角形

元の augmentation と完備化単位を保つ両端の比較を接続する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
open scoped TensorProduct
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
theorem prop247_targetH0LinearEquiv_unit_map
    (x : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj XS) :
    prop247_targetH0LinearEquiv R S B C P p hR hB f hf β hβ
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
  let e := prop247_targetTensorAlgEquiv R S B C P p hR hB f hf β hβ
  change e (completedBaseChangeTensorH0LinearEquiv R B C (p : R)
    ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
      ((derivedComplexCompletionUnit B (algebraMap R B (p : R))).app XC)
      ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map u x))) = _
  rw [prop247_completedBaseChangeTensorH0_unit]
  have hn := (boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.naturality m
  have hx : (boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.app
      (ModuleCat.of R C) ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map u x) =
    (ModuleCat.extendScalars (algebraMap R B)).map m
      ((boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.app (ModuleCat.of R S) x) :=
    congrArg (fun k => k.hom x) hn
  rw [hx, algebraScalarExtensionModuleIso_algMap_apply]
  exact RingHom.congr_fun (prop247_targetTensorAlgEquiv_comp R S B C P p hR hB f hf β hβ) _

variable [Module.Finite R S] [Algebra.FinitePresentation R S]
    (hflat : IsCompletelyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R B)))
    (N : ℕ) (hbounded : ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)

/-- 始域・終域の実比較は、元の射の完備導来底変換と元の β を結ぶ標準四角形をなす。 -/
theorem prop247_completedBaseChange_standard_square :
    (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).map
        ((boundedAboveDerivedBaseChange (algebraMap R B)).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))).hom ≫
      (prop247_targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ).hom =
    (prop247_sourceCompletedBaseChangeIso R S B p hB hflat N hbounded).hom ≫
      (moduleObjectFunctor B).map (ModuleCat.ofHom β.toLinearMap) := by
  let φ := algebraMap R B
  let F := derivedComplexCompletionFunctor B (φ (p : R))
  let η := derivedComplexCompletionUnit B (φ (p : R))
  let u := ((boundedAboveDerivedBaseChange φ).map
    (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))).hom
  let eS := prop247_sourceCompletedBaseChangeIso R S B p hB hflat N hbounded
  let eC := prop247_targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ
  let βM := ModuleCat.ofHom β.toLinearMap
  have hP : IsComplete B (φ (p : R)) ((moduleObjectFunctor B).obj (ModuleCat.of B P)) := by
    change IsModuleComplete B (φ (p : R)) (ModuleCat.of B P)
    simpa only [φ, map_natCast] using hβ.1.isModuleComplete_algebra B P p
  apply derivedComplexCompletionHom_ext B (φ (p : R)) hP
  change η.app XS ≫ (F.map u ≫ eC.hom) =
    η.app XS ≫ (eS.hom ≫ (moduleObjectFunctor B).map βM)
  rw [← Category.assoc, ← η.naturality u, Category.assoc]
  rw [← Category.assoc (η.app XS) eS.hom,
    prop247_sourceCompletedBaseChangeIso_unit]
  have : (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)).obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj _).IsLE 0
    infer_instance
  have : (XS).IsLE 0 := boundedAboveLeftDerived_isLE (ModuleCat.extendScalars φ)
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)) 0
  apply (derivedNonpositiveHomToSingleEquiv XS (ModuleCat.of B P)).injective
  simp only [derivedNonpositiveHomToSingleEquiv_apply, Functor.map_comp, Category.assoc]
  have hc := prop247_targetCompletedBaseChangeIso_homology R S B C P p hR hB f hf β hβ
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
  exact prop247_targetH0LinearEquiv_unit_map R S B C P p hR hB f hf β hβ x

/-- 原典の古典完備化からの α を用いた、元の射の実標準四角形。 -/
theorem prop247_completedBaseChange_adic_standard_square :
    (derivedComplexCompletionFunctor B (algebraMap R B (p : R))).map
        ((boundedAboveDerivedBaseChange (algebraMap R B)).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))).hom ≫
      (prop247_targetCompletedBaseChangeIso R S B C P p hR hB f hf β hβ).hom =
    (prop247_sourceCompletedAdicIso R S B p hB hflat N hbounded).hom ≫
      (moduleObjectFunctor B).map
        (ModuleCat.ofHom (prop247_completionMap p β hβ).toLinearMap) := by
  rw [prop247_completedBaseChange_standard_square R S B C P p hR hB f hf β hβ hflat N hbounded]
  dsimp only [prop247_sourceCompletedAdicIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp]
  congr 1
  apply congrArg (moduleObjectFunctor B).map
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (prop247_completionMap_unit p β hβ x).symm

end SerrePositivity.CLMST
