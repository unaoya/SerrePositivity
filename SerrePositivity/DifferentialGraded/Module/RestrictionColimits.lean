module
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects

/-! # dg加群の制限は対象ごとの余極限を保つ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z z'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

lemma moduleRestriction_comp_evaluation (x : D) :
    moduleRestriction A D E F ⋙ moduleEvaluation A D x =
      moduleEvaluation A E (F.obj (op x)).unop := by
  exact CategoryTheory.Functor.ext
    (F := moduleRestriction A D E F ⋙ moduleEvaluation A D x)
    (G := moduleEvaluation A E (F.obj (op x)).unop) (fun _ => rfl)
    (fun _ _ f => by
      change (moduleEvaluation A D x).map ((moduleRestriction A D E F).map f) =
        (moduleEvaluation A E (F.obj (op x)).unop).map f
      exact moduleRestriction_map_eval A D E F f x)

variable {J : Type z} [Category.{z'} J] [Small.{u} J]

/-- 評価の余極限保存と反映により、制限されたcoconeも余極限。 -/
def moduleRestrictionIsColimit {G : J ⥤ ModuleCategory A E} (c : Cocone G) (hc : IsColimit c) :
    IsColimit ((moduleRestriction A D E F).mapCocone c) := by
  apply moduleIsColimitOfEvaluations A D
  intro x
  change IsColimit ((moduleRestriction A D E F ⋙ moduleEvaluation A D x).mapCocone c)
  rw [moduleRestriction_comp_evaluation]
  exact isColimitOfPreserves (moduleEvaluation A E (F.obj (op x)).unop) hc

instance moduleRestrictionPreservesColimitsOfShape :
    PreservesColimitsOfShape J (moduleRestriction A D E F) where
  preservesColimit {G} :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit G)
      (moduleRestrictionIsColimit A D E F (colimit.cocone G) (colimit.isColimit G))

def moduleRestrictionColimitIso (G : J ⥤ ModuleCategory A E) :
    (moduleRestriction A D E F).obj (colimit G) ≅ colimit (G ⋙ moduleRestriction A D E F) :=
  preservesColimitIso (moduleRestriction A D E F) G

end SerrePositivity.DifferentialGraded
