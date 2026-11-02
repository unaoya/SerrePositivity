module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor

/-! # 完備化と正則な主イデアルの導来商

## 概要

標準の完備化の単位が正則な主イデアルの導来商を保つこと（`boundedAboveDerivedCompletionQuotientIso`）、別の正則な主イデアルの基底変更と可換であること、全てのスカラーの Koszul 錐と可換であること（`completionScalarConeIso`）、明示的な正則性の下で完備テンソル基底変更の剰余因子を通常の商環に取り替えられることを示す。

## 方針

比較は完備化の単位の基底変更の像で定める。座標は零因子でもよい。

## 規約

旧 `CompletionQuotient`・`CompletionQuotientBaseChange`・`CompletionScalarConeComparison`・`RegularTensorReduction`（「完備化は完全関手と可換」の型が 3 回繰り返されている。2b の B で一本化する候補）。

## 使われ方

BhattScholze、CLMST。
-/

@[expose] public noncomputable section

universe u

section CompletionQuotientPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a) (n : ℕ)
local notation "D" => DerivedCategory.Minus (ModuleCat R)
local notation "q" => Ideal.Quotient.mk (Ideal.span {a ^ n})

include ha in
/-- Scalar extension of the standard completion unit to the power quotient is an actual
isomorphism. -/
lemma boundedAboveDerivedCompletion_quotient_unit_isIso (X : D) :
    IsIso ((boundedAboveDerivedBaseChange (q)).map
      ((boundedAboveDerivedCompletionUnit R a).app X)) := by
  let f := (boundedAboveDerivedCompletionUnit R a).app X
  have hn := restrictedDerivedQuotientKoszulIso_naturality (a ^ n) (ha.pow n) f
  have hs : IsIso ((derivedScalarConeFunctor R (a ^ n)).map f.hom) :=
    derivedComplexCompletionReduction_isIso R a n X.obj
  have hi : IsIso
      (((boundedAboveDerivedRestrictScalars (q)).map
        ((boundedAboveDerivedBaseChange (q)).map f)).hom ≫
        (restrictedDerivedQuotientKoszulIso (a ^ n) (ha.pow n)
          ((boundedAboveDerivedCompletionFunctor R a).obj X)).hom) := by
    rw [hn]
    infer_instance
  have hR : IsIso (((boundedAboveDerivedRestrictScalars (q)).map
      ((boundedAboveDerivedBaseChange (q)).map f)).hom) :=
    IsIso.of_isIso_comp_right _
      (restrictedDerivedQuotientKoszulIso (a ^ n) (ha.pow n)
        ((boundedAboveDerivedCompletionFunctor R a).obj X)).hom
  have : IsIso (DerivedCategory.Minus.ι.map
      ((boundedAboveDerivedRestrictScalars (q)).map
        ((boundedAboveDerivedBaseChange (q)).map f))) := hR
  have : IsIso ((boundedAboveDerivedRestrictScalars (q)).map
      ((boundedAboveDerivedBaseChange (q)).map f)) :=
    isIso_of_reflects_iso _ DerivedCategory.Minus.ι
  exact isIso_of_reflects_iso _ (boundedAboveDerivedRestrictScalars (q))

/-- The canonical quotient comparison is the image of the standard completion unit. -/
def boundedAboveDerivedCompletionQuotientIso (X : D) :
    (boundedAboveDerivedBaseChange (q)).obj X ≅
      (boundedAboveDerivedBaseChange (q)).obj
        ((boundedAboveDerivedCompletionFunctor R a).obj X) := by
  have := boundedAboveDerivedCompletion_quotient_unit_isIso R a ha n X
  exact asIso ((boundedAboveDerivedBaseChange (q)).map
    ((boundedAboveDerivedCompletionUnit R a).app X))

/-- The canonical quotient comparison respects every morphism of actual derived objects. -/
lemma boundedAboveDerivedCompletionQuotientIso_naturality {X Y : D} (f : X ⟶ Y) :
    (boundedAboveDerivedBaseChange (q)).map f ≫
        (boundedAboveDerivedCompletionQuotientIso R a ha n Y).hom =
      (boundedAboveDerivedCompletionQuotientIso R a ha n X).hom ≫
        (boundedAboveDerivedBaseChange (q)).map
          ((boundedAboveDerivedCompletionFunctor R a).map f) := by
  change (boundedAboveDerivedBaseChange (q)).map f ≫ (boundedAboveDerivedBaseChange (q)).map _ =
    (boundedAboveDerivedBaseChange (q)).map _ ≫ (boundedAboveDerivedBaseChange (q)).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (boundedAboveDerivedBaseChange (q)).map
    ((boundedAboveDerivedCompletionUnit R a).naturality f)

/-- The image of the standard unit gives a natural isomorphism of quotient functors. -/
def boundedAboveDerivedCompletionQuotientNatIso :
    boundedAboveDerivedBaseChange (q) ≅
      boundedAboveDerivedCompletionFunctor R a ⋙ boundedAboveDerivedBaseChange (q) :=
  NatIso.ofComponents (boundedAboveDerivedCompletionQuotientIso R a ha n)
    (fun f => boundedAboveDerivedCompletionQuotientIso_naturality R a ha n f)

/-- Completed derived tensor base change with derived residue factors, without Tor assumptions. -/
def boundedAboveDerivedCompletedTensorBaseChangeNatIso :
    boundedAboveDerivedTensor ⋙ boundedAboveDerivedCompletionFunctor R a ⋙
        boundedAboveDerivedBaseChange (q) ≅
      ((boundedAboveDerivedBaseChange (q)).prod (boundedAboveDerivedBaseChange (q))) ⋙
        boundedAboveDerivedTensor :=
  Functor.isoWhiskerLeft _ (boundedAboveDerivedCompletionQuotientNatIso R a ha n).symm ≪≫
    boundedAboveDerivedTensorBaseChangeNatIso (q)

/-- Ordinary quotient rings can replace both residue factors under their separate Tor conditions. -/
def boundedAboveDerivedCompletedTensorQuotientAlgebraIso
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    (boundedAboveDerivedBaseChange (q)).obj ((boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj
          (ModuleCat.of (R ⧸ Ideal.span {a ^ n})
            (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {a ^ n}))),
          boundedAboveDerivedSingleFunctor.obj
            (ModuleCat.of (R ⧸ Ideal.span {a ^ n})
              (T ⧸ Ideal.map (algebraMap R T) (Ideal.span {a ^ n})))) :=
  (boundedAboveDerivedCompletionQuotientIso R a ha n _).symm ≪≫
    derivedTensorQuotientAlgebraIso (Ideal.span {a ^ n}) S T hS hT

/-- The completed source is the completion of the original realized module tensor construction. -/
def completedModuleTensorRealizationIso (M N : ModuleCat.{u} R) :
    ((boundedAboveDerivedCompletionFunctor R a).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))).obj ≅
      (derivedComplexCompletionFunctor R a).obj (realizedDerivedTensor R M N) :=
  (derivedComplexCompletionFunctor R a).mapIso (boundedAboveDerivedTensorModuleIso M N)

/-- The comparison with the original realized tensor preserves the standard completion unit. -/
lemma completedModuleTensorRealizationIso_unit (M N : ModuleCat.{u} R) :
    ((boundedAboveDerivedCompletionUnit R a).app
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))).hom ≫
        (completedModuleTensorRealizationIso R a M N).hom =
      (boundedAboveDerivedTensorModuleIso M N).hom ≫
        (derivedComplexCompletionUnit R a).app (realizedDerivedTensor R M N) :=
  ((derivedComplexCompletionUnit R a).naturality (boundedAboveDerivedTensorModuleIso M N).hom).symm

/-- The completed quotient comparison is natural in both algebra factors. -/
lemma boundedAboveDerivedCompletedTensorQuotientAlgebraIso_naturality
    {S S' T T' : Type u} [CommRing S] [CommRing S'] [CommRing T] [CommRing T']
    [Algebra R S] [Algebra R S'] [Algebra R T] [Algebra R T']
    (f : S →ₐ[R] S') (g : T →ₐ[R] T')
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hS' : scalarExtensionTorVanishing (q) (ModuleCat.of R S'))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hT' : scalarExtensionTorVanishing (q) (ModuleCat.of R T')) :
    (boundedAboveDerivedBaseChange (q)).map ((boundedAboveDerivedCompletionFunctor R a).map
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom g.toLinearMap))))) ≫
        (boundedAboveDerivedCompletedTensorQuotientAlgebraIso R a ha n S' T' hS' hT').hom =
      (boundedAboveDerivedCompletedTensorQuotientAlgebraIso R a ha n S T hS hT).hom ≫
        boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map
            (ModuleCat.ofHom (adicAlgebraReductionMap (Ideal.span {a ^ n}) f)))
          (boundedAboveDerivedSingleFunctor.map
            (ModuleCat.ofHom (adicAlgebraReductionMap (Ideal.span {a ^ n}) g)))) := by
  let p := boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
    (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))
    (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom g.toLinearMap)))
  have hc := (boundedAboveDerivedCompletionQuotientNatIso R a ha n).inv.naturality p
  change (boundedAboveDerivedBaseChange (q)).map
      ((boundedAboveDerivedCompletionFunctor R a).map p) ≫
      (boundedAboveDerivedCompletionQuotientIso R a ha n _).inv =
    (boundedAboveDerivedCompletionQuotientIso R a ha n _).inv ≫
      (boundedAboveDerivedBaseChange (q)).map p at hc
  simp only [boundedAboveDerivedCompletedTensorQuotientAlgebraIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [← Category.assoc, hc, Category.assoc]
  congr 1
  exact derivedTensorQuotientAlgebraIso_naturality (Ideal.span {a ^ n}) f g hS hS' hT hT'

end SerrePositivity.DerivedCompletion

end CompletionQuotientPart

section CompletionScalarConeComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a b : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Completeness for a is stable under the scalar cone for an arbitrary b. -/
lemma derivedScalarCone_isComplete (X : ConcreteDerivedCategory R)
    (hc : IsComplete R a X) :
    IsComplete R a ((derivedScalarConeFunctor R b).obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hk := isComplete_of_iso R a e.symm hc
  have hcone := isComplete_Q_mappingCone R a (smulId b K) hk hk
  exact isComplete_of_iso R a
    ((derivedScalarConeComparison R b).symm.app K ≪≫
      (derivedScalarConeFunctor R b).mapIso e) hcone

/-- The b-cone of the actual a-completion unit is an a-completion equivalence. -/
lemma scalarCone_completionUnit_map_isIso (X : D) :
    IsIso ((derivedComplexCompletionFunctor R a).map
      ((derivedScalarConeFunctor R b).map ((derivedComplexCompletionUnit R a).app X.obj))) := by
  let F := derivedComplexCompletionFunctor R a
  let f := (boundedAboveDerivedCompletionUnit R a).app X
  have hf := completionEquivalence_whiskerLeft R a f
    (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj) (boundedAboveKoszulObject b)
  have hn := boundedAboveDerivedTensorKoszulIso_naturality b f
  let eX := boundedAboveDerivedTensorKoszulIso b X
  let eY := boundedAboveDerivedTensorKoszulIso b
    ((boundedAboveDerivedCompletionFunctor R a).obj X)
  change (boundedAboveKoszulObject b ◁ f).hom ≫ eY.hom =
    eX.hom ≫ (derivedScalarConeFunctor R b).map f.hom at hn
  have he : IsIso (F.map eX.hom ≫ F.map ((derivedScalarConeFunctor R b).map f.hom)) := by
    rw [← F.map_comp]
    rw [← hn, F.map_comp]
    exact inferInstance
  dsimp only [f, boundedAboveDerivedCompletionUnit, ObjectProperty.homMk] at he
  exact IsIso.of_isIso_comp_left (F.map eX.hom) _

/-- Extend the original scalar-cone unit to the complete scalar-cone target. -/
def completionScalarConeComparison (X : D) :
    (derivedComplexCompletionFunctor R a).obj ((derivedScalarConeFunctor R b).obj X.obj) ⟶
      (derivedScalarConeFunctor R b).obj ((derivedComplexCompletionFunctor R a).obj X.obj) :=
  (derivedComplexCompletionFunctor R a).map
      ((derivedScalarConeFunctor R b).map ((derivedComplexCompletionUnit R a).app X.obj)) ≫
    (derivedComplexCompletionUnitIso R a _
      (derivedScalarCone_isComplete R a b _
        (derivedComplexCompletionFunctor_isComplete R a X.obj))).inv

/-- This extension has exactly the original scalar-cone completion-unit diagram. -/
lemma completionScalarConeComparison_unit (X : D) :
    (derivedComplexCompletionUnit R a).app ((derivedScalarConeFunctor R b).obj X.obj) ≫
        completionScalarConeComparison R a b X =
      (derivedScalarConeFunctor R b).map ((derivedComplexCompletionUnit R a).app X.obj) :=
  (derivedComplexCompletionHomEquiv R a _ _
    (derivedScalarCone_isComplete R a b _
      (derivedComplexCompletionFunctor_isComplete R a X.obj))).apply_symm_apply _

/-- Actual a-completion and the b-cone commute by the original unit-normalized map. -/
lemma completionScalarConeComparison_isIso (X : D) :
    IsIso (completionScalarConeComparison R a b X) := by
  dsimp only [completionScalarConeComparison]
  have := scalarCone_completionUnit_map_isIso R a b X
  infer_instance

/-- The standard comparison is an isomorphism of the original derived objects. -/
def completionScalarConeIso (X : D) :
    (derivedComplexCompletionFunctor R a).obj ((derivedScalarConeFunctor R b).obj X.obj) ≅
      (derivedScalarConeFunctor R b).obj ((derivedComplexCompletionFunctor R a).obj X.obj) := by
  have := completionScalarConeComparison_isIso R a b X
  exact asIso (completionScalarConeComparison R a b X)

/-- Reflection uniqueness preserves every original bounded-above derived morphism. -/
lemma completionScalarConeComparison_naturality {X Y : D} (f : X ⟶ Y) :
    (derivedComplexCompletionFunctor R a).map ((derivedScalarConeFunctor R b).map f.hom) ≫
        completionScalarConeComparison R a b Y =
      completionScalarConeComparison R a b X ≫
        (derivedScalarConeFunctor R b).map ((derivedComplexCompletionFunctor R a).map f.hom) := by
  apply derivedComplexCompletionHom_ext R a
    (derivedScalarCone_isComplete R a b _ (derivedComplexCompletionFunctor_isComplete R a Y.obj))
  have hr := (derivedComplexCompletionUnit R a).naturality
    ((derivedScalarConeFunctor R b).map f.hom)
  simp only [Functor.id_map] at hr
  rw [← Category.assoc, ← hr, Category.assoc, completionScalarConeComparison_unit,
    ← Category.assoc, completionScalarConeComparison_unit,
    ← Functor.map_comp, ← Functor.map_comp]
  simpa only [Functor.id_map] using congrArg (derivedScalarConeFunctor R b).map
    ((derivedComplexCompletionUnit R a).naturality f.hom)

/-- The unit-normalized comparisons assemble into a natural isomorphism. -/
def completionScalarConeNatIso :
    DerivedCategory.Minus.ι ⋙ derivedScalarConeFunctor R b ⋙ derivedComplexCompletionFunctor R a ≅
      DerivedCategory.Minus.ι ⋙ derivedComplexCompletionFunctor R a ⋙ derivedScalarConeFunctor R b :=
  NatIso.ofComponents (completionScalarConeIso R a b)
    (fun f => completionScalarConeComparison_naturality R a b f)

end SerrePositivity.DerivedCompletion

end CompletionScalarConeComparisonPart

section CompletionQuotientBaseChangePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard

/-- Coefficient restriction preserves and reflects the actual derived completeness condition. -/
lemma derivedRestrictScalars_isComplete_iff {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (Y : ConcreteDerivedCategory S) :
    IsComplete R a ((derivedRestrictScalars φ).obj Y) ↔ IsComplete S (φ a) Y := by
  constructor
  · intro h
    apply (isComplete_iff_derivedComplexCompletionUnit_isIso S (φ a) Y).mpr
    have := derivedComplexCompletionUnit_isIso_of_isComplete R a _ h
    have hn := derivedRestrictionCompletionIso_unit φ a Y
    have : IsIso ((derivedRestrictScalars φ).map
        ((derivedComplexCompletionUnit S (φ a)).app Y) ≫
        (derivedRestrictionCompletionIso φ a).hom.app Y) := by
      rw [hn]
      infer_instance
    have : IsIso ((derivedRestrictScalars φ).map
        ((derivedComplexCompletionUnit S (φ a)).app Y)) :=
      IsIso.of_isIso_comp_right _ ((derivedRestrictionCompletionIso φ a).hom.app Y)
    exact isIso_of_reflects_iso _ (derivedRestrictScalars φ)
  · exact derivedRestrictScalars_isComplete φ a Y

variable (R : Type u) [CommRing R] (a b : R) (hb : IsSMulRegular R b)
local notation "D" => DerivedCategory.Minus (ModuleCat R)
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {b})
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {b}

include hb in
/-- Derived quotient by a regular b preserves completeness for an arbitrary a. -/
lemma derivedBaseChange_principal_isComplete (X : D) (hc : IsComplete R a X.obj) :
    IsComplete Q ((q) a) ((boundedAboveDerivedBaseChange (q)).obj X).obj := by
  apply (derivedRestrictScalars_isComplete_iff (q) a _).mp
  exact isComplete_of_iso R a (restrictedDerivedQuotientKoszulIso b hb X).symm
    (derivedScalarCone_isComplete R a b X.obj hc)

include hb in
/-- The original quotient of the a-completion unit is an a-completion equivalence over Q. -/
lemma completionQuotientUnit_map_isIso (X : D) :
    IsIso ((derivedComplexCompletionFunctor Q ((q) a)).map
      (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X)).hom)) := by
  let F := derivedComplexCompletionFunctor R a
  let f := (boundedAboveDerivedCompletionUnit R a).app X
  let g := ((boundedAboveDerivedBaseChange (q)).map f).hom
  let eX := restrictedDerivedQuotientKoszulIso b hb X
  let eY := restrictedDerivedQuotientKoszulIso b hb
    ((boundedAboveDerivedCompletionFunctor R a).obj X)
  have hn := restrictedDerivedQuotientKoszulIso_naturality b hb f
  change (derivedRestrictScalars (q)).map g ≫ eY.hom =
    eX.hom ≫ (derivedScalarConeFunctor R b).map f.hom at hn
  have hi := scalarCone_completionUnit_map_isIso R a b X
  have hi' : IsIso (F.map ((derivedScalarConeFunctor R b).map f.hom)) := by
    dsimp only [f, boundedAboveDerivedCompletionUnit, ObjectProperty.homMk]
    exact hi
  have hleft : IsIso (F.map ((derivedRestrictScalars (q)).map g) ≫ F.map eY.hom) := by
    rw [← F.map_comp, hn, F.map_comp]
    infer_instance
  have hrestricted : IsIso (F.map ((derivedRestrictScalars (q)).map g)) :=
    IsIso.of_isIso_comp_right _ (F.map eY.hom)
  have : IsIso ((derivedRestrictScalars (q)).map
      ((derivedComplexCompletionFunctor Q ((q) a)).map g)) :=
    (NatIso.isIso_map_iff (derivedRestrictionCompletionIso (q) a) g).mpr hrestricted
  exact isIso_of_reflects_iso _ (derivedRestrictScalars (q))

/-- Extend the original quotient of the completion unit over the quotient ring. -/
def completionQuotientBaseChangeComparison (X : D) :
    (derivedComplexCompletionFunctor Q ((q) a)).obj ((boundedAboveDerivedBaseChange (q)).obj X).obj ⟶
      ((boundedAboveDerivedBaseChange (q)).obj
        ((boundedAboveDerivedCompletionFunctor R a).obj X)).obj :=
  (derivedComplexCompletionFunctor Q ((q) a)).map
      (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X)).hom) ≫
    (derivedComplexCompletionUnitIso Q ((q) a) _
      (derivedBaseChange_principal_isComplete R a b hb _
        (derivedComplexCompletionFunctor_isComplete R a X.obj))).inv

/-- The Q-linear comparison preserves the original base-change completion unit. -/
lemma completionQuotientBaseChangeComparison_unit (X : D) :
    (derivedComplexCompletionUnit Q ((q) a)).app ((boundedAboveDerivedBaseChange (q)).obj X).obj ≫
        completionQuotientBaseChangeComparison R a b hb X =
      (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X)).hom) :=
  (derivedComplexCompletionHomEquiv Q ((q) a) _ _
    (derivedBaseChange_principal_isComplete R a b hb _
      (derivedComplexCompletionFunctor_isComplete R a X.obj))).apply_symm_apply _

/-- The original comparison is an actual derived isomorphism over the quotient coefficient ring. -/
lemma completionQuotientBaseChangeComparison_isIso (X : D) :
    IsIso (completionQuotientBaseChangeComparison R a b hb X) := by
  dsimp only [completionQuotientBaseChangeComparison]
  have := completionQuotientUnit_map_isIso R a b hb X
  infer_instance

/-- Completion and regular principal base change commute on the original derived objects. -/
def completionQuotientBaseChangeIso (X : D) :
    (derivedComplexCompletionFunctor Q ((q) a)).obj ((boundedAboveDerivedBaseChange (q)).obj X).obj ≅
      ((boundedAboveDerivedBaseChange (q)).obj
        ((boundedAboveDerivedCompletionFunctor R a).obj X)).obj := by
  have := completionQuotientBaseChangeComparison_isIso R a b hb X
  exact asIso (completionQuotientBaseChangeComparison R a b hb X)

end SerrePositivity.DerivedCompletion

end CompletionQuotientBaseChangePart

section RegularTensorReductionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a) (n : ℕ)
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (hS : IsSMulRegular S a) (hT : IsSMulRegular T a)
local notation "q" => Ideal.Quotient.mk (Ideal.span {a ^ n})

end SerrePositivity.DerivedCompletion

end RegularTensorReductionPart
