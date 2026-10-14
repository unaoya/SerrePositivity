module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison

/-! # The standard completion unit preserves regular principal derived quotients

These comparisons use the actual scalar-extension functor over R/(a^n).
Replacing derived residue factors by ordinary quotient rings retains both Tor conditions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
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
