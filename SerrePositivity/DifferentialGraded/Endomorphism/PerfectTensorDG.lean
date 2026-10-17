module
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectTensor
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectDGComparison

/-! # U13の実際のdg enhancementへの再構成tensorの制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

lemma perfectEndomorphismTensorDG_obj_perfect (N : PerfectDGModule A (EndomorphismObject E.val)) :
    modulePerfectOver A D S ((moduleToDerived A D).obj
      ((endomorphismModuleTensor A D E.val).onClosed.obj
        (ForgetEnrichment.of (Complex A) N.val))) :=
  (modulePerfectOver A D S).prop_of_iso
    (endomorphismDerivedTensorProjectiveComputation A D E.val
      (ForgetEnrichment.of (Complex A) N.val) N.property.1)
    (perfectEndomorphismTensor_obj_perfect A D S E N.property.2)

/-- 対象は実際のunderived tensorであり、射影性とperfect性を証拠として保持する。 -/
def perfectEndomorphismTensorDG :
    DGFunctor A (PerfectDGModule A (EndomorphismObject E.val)) (PerfectDGModuleOver A D S) where
  obj N := ⟨(endomorphismModuleTensor A D E.val).obj N.val,
    endomorphismModuleTensor_homotopicallyProjective A D E.val E.property.1 N.property.1,
    perfectEndomorphismTensorDG_obj_perfect A D S E N⟩
  map N N' := (endomorphismModuleTensor A D E.val).map N.val N'.val
  map_id N := (endomorphismModuleTensor A D E.val).map_id N.val
  map_comp N N' N'' := (endomorphismModuleTensor A D E.val).map_comp N.val N'.val N''.val

lemma perfectEndomorphismTensorDG_inclusion_square :
    (perfectEndomorphismTensorDG A D S E).comp (perfectDGModuleInclusion A D S) =
      (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).comp
        (endomorphismModuleTensor A D E.val) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (perfectEndomorphismTensorDG A D S E).comp (perfectDGModuleInclusion A D S))
    (G := (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).comp
      (endomorphismModuleTensor A D E.val)) (fun _ => rfl)
  intro N N'
  simp only [eqToHom_refl, Category.comp_id]
  exact (Category.id_comp _).symm

end SerrePositivity.DifferentialGraded
