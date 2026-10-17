module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleDGFunctor
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic

/-! # 実際に係数変更した加群のEndとのdg比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D] (E : RightModule A D)

/-- 元のEndの係数変更から、実際の係数変更加群のEndへ向かう比較。 -/
def actualScalarEnd :
    DGFunctor A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (EndomorphismObject (ScalarExtension.rightModule φ D E)) where
  obj _ := .point
  map _ _ := scalarModuleHom φ D E E
  map_id _ := scalarModuleHom_identity φ D E
  map_comp _ _ _ := scalarModuleHom_composition φ D E E E

/-- 実際の加群圏へのEnd包含正方形。 -/
lemma actualScalarEnd_inclusion_square :
    (actualScalarEnd φ D E).comp
        (endomorphismInclusion A' (ScalarExtension.rightModule φ D E)) =
      (ScalarExtension.dgFunctor φ (endomorphismInclusion A E)).comp
        (scalarModuleDGFunctor φ D) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (actualScalarEnd φ D E).comp
      (endomorphismInclusion A' (ScalarExtension.rightModule φ D E)))
    (G := (ScalarExtension.dgFunctor φ (endomorphismInclusion A E)).comp
      (scalarModuleDGFunctor φ D)) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, actualScalarEnd,
    endomorphismInclusion, scalarModuleDGFunctor, ScalarExtension.dgFunctor,
    CategoryTheory.Functor.map_id, Category.comp_id, eqToHom_refl]
  exact (Category.id_comp _).symm

/-- 評価も係数変更前の評価と既存の複体dg係数変更に接続する。 -/
lemma scalarModuleDGFunctor_evaluation_square (x : D) :
    (scalarModuleDGFunctor φ D).comp
        (moduleEvaluationDG A' (ScalarExtension.DGBaseChange φ D) x) =
      (ScalarExtension.dgFunctor φ (moduleEvaluationDG A D x)).comp
        (ScalarExtension.complexDGFunctor φ) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (scalarModuleDGFunctor φ D).comp
      (moduleEvaluationDG A' (ScalarExtension.DGBaseChange φ D) x))
    (G := (ScalarExtension.dgFunctor φ (moduleEvaluationDG A D x)).comp
      (ScalarExtension.complexDGFunctor φ)) (fun _ => rfl)
  intro M N
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id]
  exact scalarModuleHom_π φ D M N x

end SerrePositivity.DifferentialGraded
