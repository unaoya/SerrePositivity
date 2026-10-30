module
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # The two-term free model of a regular principal quotient

Regularity is used only for the injectivity of multiplication on the original ring.
The quotient module uses the precise scalar-restriction structure of derived base change.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The standard quotient map into the scalar module used by derived scalar extension. -/
def principalQuotientLinearMap (a : R) :
    R →ₗ[R] baseChangeScalarModule (Ideal.Quotient.mk (Ideal.span {a})) where
  toFun := Ideal.Quotient.mk (Ideal.span {a})
  map_add' := map_add _
  map_smul' r x := by
    change Ideal.Quotient.mk (Ideal.span {a}) (r * x) =
      Ideal.Quotient.mk (Ideal.span {a}) r * Ideal.Quotient.mk (Ideal.span {a}) x
    exact map_mul _ r x

/-- The canonical module presentation, with no regularity assumed yet. -/
def principalQuotientPresentation (a : R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (a • 𝟙 (ModuleCat.of R R)) (ModuleCat.ofHom (principalQuotientLinearMap a)) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Ideal.Quotient.mk (Ideal.span {a}) (a * x) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _)))

/-- Regularity makes the presentation short exact; units and zero rings are allowed. -/
lemma principalQuotientPresentation_shortExact (a : R) (ha : IsSMulRegular R a) :
    (principalQuotientPresentation a).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    change Ideal.Quotient.mk (Ideal.span {a}) y = 0 at hy
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hy)
    exact ⟨x, hx.symm⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr ha
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
    change Function.Surjective (Ideal.Quotient.mk (Ideal.span {a}))
    exact Ideal.Quotient.mk_surjective)

/-- The presentation as a short complex of degree-zero cochain complexes. -/
def principalQuotientCochainPresentation (a : R) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (principalQuotientPresentation a).map (CochainComplex.singleFunctor (ModuleCat R) 0)

lemma principalQuotientCochainPresentation_f (a : R) :
    (principalQuotientCochainPresentation a).f = smulId a (cochainTensorUnit (R := R)) := by
  change (CochainComplex.singleFunctor (ModuleCat R) 0).map (a • 𝟙 (ModuleCat.of R R)) = _
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- The standard augmentation from the two-term free complex to the actual quotient module. -/
def principalQuotientResolutionAugmentation (a : R) :
    CochainComplex.mappingCone (smulId a (cochainTensorUnit (R := R))) ⟶
      cochainSingleZero (baseChangeScalarModule (Ideal.Quotient.mk (Ideal.span {a}))) :=
  eqToHom (congrArg (fun f : cochainTensorUnit (R := R) ⟶ cochainTensorUnit (R := R) =>
    CochainComplex.mappingCone f) (principalQuotientCochainPresentation_f a).symm) ≫
    CochainComplex.mappingCone.descShortComplex (principalQuotientCochainPresentation a)

/-- Under regularity, the two-term augmentation is a quasi-isomorphism. -/
lemma principalQuotientResolutionAugmentation_quasiIso (a : R) (ha : IsSMulRegular R a) :
    QuasiIso (principalQuotientResolutionAugmentation a) := by
  have hS : (principalQuotientCochainPresentation a).ShortExact :=
    (principalQuotientPresentation_shortExact a ha).map_of_exact
      (CochainComplex.singleFunctor (ModuleCat R) 0)
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  dsimp only [principalQuotientResolutionAugmentation]
  infer_instance

/-- The regular quotient has the explicit two-term bounded-above projective model. -/
def principalQuotientDerivedModel (a : R) (ha : IsSMulRegular R a) :
    BoundedAboveDerivedModel
      (derivedBaseChangeScalarObject (Ideal.Quotient.mk (Ideal.span {a}))).obj where
  complex := CochainComplex.mappingCone (smulId a (cochainTensorUnit (R := R)))
  bound := 0
  bounded := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨CochainComplex.isZero_of_isStrictlyLE cochainTensorUnit 0 (i + 1) (by omega),
      CochainComplex.isZero_of_isStrictlyLE cochainTensorUnit 0 i hi⟩
  projective i := Projective.of_iso
    (homotopyCofiber.XIsoBiprod (smulId a (cochainTensorUnit (R := R))) i (i + 1) rfl).symm
    inferInstance
  iso := by
    have := principalQuotientResolutionAugmentation_quasiIso a ha
    exact asIso (DerivedCategory.Q.map (principalQuotientResolutionAugmentation a))

end SerrePositivity
