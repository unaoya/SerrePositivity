module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterComposition

/-! # Categories of maps with a shared arbitrary simplicial parameter -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.ParameterCategory

structure Object (T : SSet.{v}) where
  value : SSet.{v}

instance (T : SSet.{v}) : Category.{v} (Object T) where
  Hom X Y := X.value ⊗ T ⟶ Y.value
  id X := ParameterComposition.const T (𝟙 X.value)
  comp f g := ParameterComposition.comp f g
  id_comp := ParameterComposition.id_comp
  comp_id := ParameterComposition.comp_id
  assoc := ParameterComposition.assoc

def reindex {T U : SSet.{v}} (j : U ⟶ T) : Object T ⥤ Object U where
  obj X := ⟨X.value⟩
  map f := ParameterComposition.substitute j f
  map_id _ := ParameterComposition.substitute_const j _
  map_comp f g := ParameterComposition.substitute_comp j f g

lemma reindex_id (T : SSet.{v}) : reindex (𝟙 T) = 𝟭 (Object T) := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

lemma reindex_comp {T U V : SSet.{v}} (j : U ⟶ T) (k : V ⟶ U) :
    reindex (k ≫ j) = reindex j ⋙ reindex k := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

end SerrePositivity.SimplicialModel.ParameterCategory
