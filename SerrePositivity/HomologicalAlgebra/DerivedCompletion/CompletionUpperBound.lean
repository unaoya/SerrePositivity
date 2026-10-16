module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorSequence

/-! # Principal derived completion preserves the same cohomological upper bound -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

lemma complexPowerKoszulStage_homology_isZero_of_gt
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero (K.homology i)) (n : ℕ) (i : ℤ) (hi : b < i) :
    IsZero ((complexPowerKoszulStage R a K n).homology i) :=
  (SerrePositivity.Cone.exact₃ (smulId (a ^ n) K) i (i + 1) rfl).isZero_of_both_isZero
    (hK i hi) (hK (i + 1) (by omega))

/-- The top homology transition is surjective, even when a is a zero divisor. -/
lemma complexPowerKoszulTransition_homology_top_surjective
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hK : IsZero (K.homology (b + 1))) (n : ℕ) :
    Function.Surjective (homologyMap (complexPowerKoszulTransition R a K n) b) := by
  have he := SerrePositivity.Cone.exact₃ (smulId (a ^ n) K) b (b + 1) rfl
  have hep : Epi (homologyMap (CochainComplex.mappingCone.inr (smulId (a ^ n) K)) b) :=
    he.epi_f (hK.eq_of_tgt _ _)
  have hw := congrArg (fun f ↦ homologyMap f b)
    (complexPowerKoszulInclusion_compatible R a K n)
  rw [homologyMap_comp] at hw
  have ht : Epi (homologyMap (complexPowerKoszulTransition R a K n) b) := epi_of_epi_fac hw
  exact (ModuleCat.epi_iff_surjective _).mp ht

lemma complexCompletion_homology_isZero_of_gt
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero (K.homology i)) (i : ℤ) (hi : b < i) :
    IsZero (((complexCompletionFunctor R a).obj K).homology i) := by
  have hdiff : Function.Surjective (complexTowerHomologyDifference R
      (complexPowerKoszulStage R a K) (complexPowerKoszulTransition R a K) (i - 1)) := by
    apply moduleTowerDifference_surjective
    intro n
    by_cases ht : i - 1 = b
    · rw [ht]
      exact complexPowerKoszulTransition_homology_top_surjective R a K b
        (hK (b + 1) (by omega)) n
    · intro y
      have hz := complexPowerKoszulStage_homology_isZero_of_gt R a K b hK n (i - 1) (by omega)
      exact ⟨0, (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _⟩
  have hinj := complexTowerMilnorProjection_injective_of_surjective R _ _ i hdiff
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ hinj ?_⟩
  apply Subtype.ext
  funext n
  exact (ModuleCat.isZero_iff_subsingleton.mp
    (complexPowerKoszulStage_homology_isZero_of_gt R a K b hK n i hi)).elim _ _

/-- The actual unbounded derived completion preserves every same upper bound. -/
theorem derivedComplexCompletionFunctor_isLE (X : ConcreteDerivedCategory R) (b : ℤ)
    (hX : X.IsLE b) : ((derivedComplexCompletionFunctor R a).obj X).IsLE b := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hK (i : ℤ) (hi : b < i) : IsZero (K.homology i) := by
    have hz := (DerivedCategory.isLE_iff _ _).mp hX i hi
    exact hz.of_iso (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e)
  let ef : DerivedCategory.Q.obj ((complexCompletionFunctor R a).obj K) ≅
      (derivedComplexCompletionFunctor R a).obj X :=
    (derivedComplexCompletionComparison R a).symm.app K ≪≫
      (derivedComplexCompletionFunctor R a).mapIso e
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  have hz := complexCompletion_homology_isZero_of_gt R a K b hK i hi
  have hzQ := hz.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _)
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso ef).isZero_iff.mp hzQ

/-- G11-1: the existing bounded-above completion preserves the same upper bound. -/
theorem boundedAboveDerivedCompletionFunctor_isLE
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (b : ℤ) (hX : X.obj.IsLE b) :
    ((boundedAboveDerivedCompletionFunctor R a).obj X).obj.IsLE b :=
  derivedComplexCompletionFunctor_isLE R a X.obj b hX

end SerrePositivity.DerivedCompletion
