module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.RingGradedSplit
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom

/-! 複体の指定余極限を同じ一点加群の指定余極限へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (A : Type u) [CommRing A]

def ringComplexFunctor : Complex A ⥤ ModuleCategory A PUnit.{1} where
  obj P := ForgetEnrichment.of (Complex A) (ringModule A P)
  map f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap A f
  map_id P := by
    apply (moduleEvaluation A PUnit.{1} PUnit.unit).map_injective
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap_evaluation, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply (moduleEvaluation A PUnit.{1} PUnit.unit).map_injective
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap_evaluation, CategoryTheory.Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap_evaluation, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap_evaluation]

lemma ringComplexFunctor_comp_evaluation :
    ringComplexFunctor A ⋙ moduleEvaluation A PUnit.{1} PUnit.unit = 𝟭 (Complex A) := by
  exact CategoryTheory.Functor.ext (fun _ => rfl)
    (fun _ _ f => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap_evaluation A f)

def ringComplexIsColimit {J : Type w} [Category.{w'} J] [Small.{u} J]
    {F : J ⥤ Complex A} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((ringComplexFunctor A).mapCocone c) := by
  apply moduleIsColimitOfEvaluations A PUnit.{1}
  intro x
  cases x
  change IsColimit ((ringComplexFunctor A ⋙
    moduleEvaluation A PUnit.{1} PUnit.unit).mapCocone c)
  rw [ringComplexFunctor_comp_evaluation]
  exact hc

instance ringComplexFunctor_preservesColimitsOfShape
    (J : Type w) [Category.{w'} J] [Small.{u} J] :
    PreservesColimitsOfShape J (ringComplexFunctor A) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone
    (colimit.isColimit F) (ringComplexIsColimit A (colimit.isColimit F))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
