module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Localization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES

/-! # Complexes with derived complete terms are derived complete

The localization telescope has length one. Its Hom complex is the scalar
homotopy-limit tower, whose difference is a termwise isomorphism by the
recurrence criterion. No boundedness of the complex is needed.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- The scalar-tower difference is an actual isomorphism when every term is
derived complete. -/
lemma scalarComplexTowerDifference_isIso_of_terms
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, IsModuleComplete R a (K.X i)) :
    IsIso (complexTowerDifference R (constantComplexTower R K) (fun _ => smulId a K)) := by
  let d := complexTowerDifference R (constantComplexTower R K) (fun _ => smulId a K)
  have he (i : ℤ) (x : (piObj (constantComplexTower R K)).X i) :
      complexProductDegreeEquiv R (constantComplexTower R K) i (d.f i x) =
        adicRecurrenceMap (M := K.X i) a
          (complexProductDegreeEquiv R (constantComplexTower R K) i x) := by
    funext n
    exact complexProductDegreeEquiv_difference R _ _ i x n
  have hIso (i : ℤ) : IsIso (d.f i) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let e := complexProductDegreeEquiv R (constantComplexTower R K) i
    have hb := (isModuleComplete_iff_recurrence_bijective R a (K.X i)).mp (hK i)
    constructor
    · intro x y hxy
      apply e.injective
      apply hb.injective
      rw [← he i x, ← he i y, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hb.surjective (e y)
      refine ⟨e.symm z, e.injective ?_⟩
      rw [he]
      exact (congrArg (adicRecurrenceMap (M := K.X i) a) (e.apply_symm_apply z)).trans hz
  exact HomologicalComplex.Hom.isIso_of_components d

/-- Termwise derived completeness implies completeness of the actual derived
image of an arbitrary cochain complex. -/
lemma isComplete_Q_of_terms
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, IsModuleComplete R a (K.X i)) :
    IsComplete R a (DerivedCategory.Q.obj K) := by
  apply (isComplete_iff_scalarComplexTowerHomotopyLimit_acyclic R a K).mpr
  have := scalarComplexTowerDifference_isIso_of_terms R a K hK
  exact cochainAcyclic_shift
    ((cochain_quasiIso_iff_cone_acyclic _).mp inferInstance) (-1)

end SerrePositivity.DerivedCompletion
