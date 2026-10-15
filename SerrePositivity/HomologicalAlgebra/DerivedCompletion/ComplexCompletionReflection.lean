module

public import SerrePositivity.HomologicalAlgebra.CoaugmentedReflection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReduction

/-! # The Hom universal property of actual principal derived completion -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- Completion inverts a map whenever all its power-Koszul reductions are quasi-isomorphisms. -/
theorem complexCompletionFunctor_map_quasiIso_of_koszul
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hf : ∀ n : ℕ, QuasiIso ((scalarConeFunctor (a ^ n)).map f)) :
    QuasiIso ((complexCompletionFunctor R a).map f) := by
  change QuasiIso
    (((cochainMappingConeFunctor R).map
      ((complexPowerKoszulDifferenceFunctor R a).map f))⟦(-1 : ℤ)⟧')
  apply (CochainComplex.quasiIso_shift_iff _ _).mpr
  have h : QuasiIso ((complexPowerKoszulProductFunctor R a).map f) :=
    complexTowerProductMap_quasiIso R _ hf
  have : QuasiIso (((complexPowerKoszulDifferenceFunctor R a).map f).left) := h
  have : QuasiIso (((complexPowerKoszulDifferenceFunctor R a).map f).right) := h
  exact cochainMappingConeFunctor_map_quasiIso R
    ((complexPowerKoszulDifferenceFunctor R a).map f)

/-- Applying completion to its own standard unit is a quasi-isomorphism on complexes. -/
theorem complexCompletionFunctor_map_unit_quasiIso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIso ((complexCompletionFunctor R a).map (complexCompletionUnit R a K)) :=
  complexCompletionFunctor_map_quasiIso_of_koszul R a _
    (complexCompletionUnit_koszul_quasiIso R a K)

/-- The actual derived completion functor inverts its standard unit. -/
theorem derivedComplexCompletionFunctor_map_unit_isIso
    (X : ConcreteDerivedCategory R) :
    IsIso ((derivedComplexCompletionFunctor R a).map
      ((derivedComplexCompletionUnit R a).app X)) := by
  let F := derivedComplexCompletionFunctor R a
  let η := derivedComplexCompletionUnit R a
  have hQ (K : CochainComplex (ModuleCat.{u} R) ℤ) :
      IsIso (F.map (η.app (DerivedCategory.Q.obj K))) := by
    have := complexCompletionFunctor_map_unit_quasiIso R a K
    have hn := (derivedComplexCompletionComparison R a).hom.naturality
      (complexCompletionUnit R a K)
    change F.map (DerivedCategory.Q.map (complexCompletionUnit R a K)) ≫
      (derivedComplexCompletionComparison R a).hom.app
        ((complexCompletionFunctor R a).obj K) =
      (derivedComplexCompletionComparison R a).hom.app K ≫
        DerivedCategory.Q.map ((complexCompletionFunctor R a).map
          (complexCompletionUnit R a K)) at hn
    have hunit : IsIso (F.map (DerivedCategory.Q.map (complexCompletionUnit R a K))) := by
      have : IsIso (F.map (DerivedCategory.Q.map (complexCompletionUnit R a K)) ≫
          (derivedComplexCompletionComparison R a).hom.app
            ((complexCompletionFunctor R a).obj K)) := by
        rw [hn]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        ((derivedComplexCompletionComparison R a).hom.app
          ((complexCompletionFunctor R a).obj K))
    have he := congrArg F.map (derivedComplexCompletionUnit_comparison R a K)
    rw [F.map_comp] at he
    have : IsIso (F.map (η.app (DerivedCategory.Q.obj K)) ≫
        F.map ((derivedComplexCompletionComparison R a).hom.app K)) := by
      rw [he]
      exact hunit
    exact IsIso.of_isIso_comp_right _
      (F.map ((derivedComplexCompletionComparison R a).hom.app K))
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have := hQ K
  have hn := congrArg F.map (η.naturality e.hom)
  simp only [Functor.id_map, F.map_comp] at hn
  have : IsIso (F.map e.hom ≫ F.map (η.app X)) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map e.hom) (F.map (η.app X))

/-- The two iterated standard units agree on the actual derived category. -/
theorem derivedComplexCompletionUnit_comm (X : ConcreteDerivedCategory R) :
    (derivedComplexCompletionFunctor R a).map ((derivedComplexCompletionUnit R a).app X) =
      (derivedComplexCompletionUnit R a).app ((derivedComplexCompletionFunctor R a).obj X) := by
  apply coaugmentedUnit_comm_of_isIso
  · intro Y
    exact derivedComplexCompletionUnit_isIso_of_isComplete R a _
      (derivedComplexCompletionFunctor_isComplete R a Y)
  · exact derivedComplexCompletionFunctor_map_unit_isIso R a

/-- Precomposition with the actual standard unit is a bijection into every complete target. -/
def derivedComplexCompletionHomEquiv (X Y : ConcreteDerivedCategory R)
    (hY : IsComplete R a Y) :
    ((derivedComplexCompletionFunctor R a).obj X ⟶ Y) ≃ (X ⟶ Y) := by
  have := derivedComplexCompletionUnit_isIso_of_isComplete R a Y hY
  exact coaugmentedHomEquiv _ _ (derivedComplexCompletionUnit_comm R a) X Y

@[simp] theorem derivedComplexCompletionHomEquiv_apply (X Y : ConcreteDerivedCategory R)
    (hY : IsComplete R a Y) (f : (derivedComplexCompletionFunctor R a).obj X ⟶ Y) :
    derivedComplexCompletionHomEquiv R a X Y hY f =
      (derivedComplexCompletionUnit R a).app X ≫ f := rfl

/-- The extension is computed using the original completion functor and standard unit. -/
@[simp] theorem derivedComplexCompletionHomEquiv_symm_apply
    (X Y : ConcreteDerivedCategory R) (hY : IsComplete R a Y) (f : X ⟶ Y) :
    (derivedComplexCompletionHomEquiv R a X Y hY).symm f =
      (derivedComplexCompletionFunctor R a).map f ≫
        (derivedComplexCompletionUnitIso R a Y hY).inv := rfl

/-- Maps to a complete target are equal if they agree along the standard completion unit. -/
theorem derivedComplexCompletionHom_ext {X Y : ConcreteDerivedCategory R}
    (hY : IsComplete R a Y)
    {f g : (derivedComplexCompletionFunctor R a).obj X ⟶ Y}
    (h : (derivedComplexCompletionUnit R a).app X ≫ f =
      (derivedComplexCompletionUnit R a).app X ≫ g) : f = g :=
  (derivedComplexCompletionHomEquiv R a X Y hY).injective h

/-- Every map to a complete target has a unique extension along the actual standard unit. -/
theorem derivedComplexCompletion_existsUnique_extension
    {X Y : ConcreteDerivedCategory R} (hY : IsComplete R a Y) (f : X ⟶ Y) :
    ∃! g : (derivedComplexCompletionFunctor R a).obj X ⟶ Y,
      (derivedComplexCompletionUnit R a).app X ≫ g = f := by
  let e := derivedComplexCompletionHomEquiv R a X Y hY
  refine ⟨e.symm f, e.apply_symm_apply f, ?_⟩
  intro g hg
  exact e.injective (hg.trans (e.apply_symm_apply f).symm)

end SerrePositivity.DerivedCompletion
