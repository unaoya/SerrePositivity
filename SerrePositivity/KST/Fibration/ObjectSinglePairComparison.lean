module
public import SerrePositivity.KST.SConstruction.RelativeAdditivity
public import SerrePositivity.KST.SConstruction.SingleRealizationAdditivity

/-! # 元の object S の射対から単回実現の同じ射対への比較 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- object S から同じ単回多重実現への元の自然な比較。 -/
def objectSingleComparison : objectSConstructionFunctor.{u} ⟶ multiRealizationFunctor 1 where
  app X := objectCoreRealizationComparison.app X ≫ (coreSingleRealizationIso X).hom
  naturality {X Y} f := by
    rw [← Category.assoc, objectCoreRealizationComparison.naturality f, Category.assoc,
      coreSingleRealizationIso_naturality, ← Category.assoc]

/-- 元の object/単回実現比較は局所化同型。 -/
lemma objectSingleComparison_localized_isIso (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (objectSingleComparison.app X)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (objectCoreRealizationComparison.app X)) :=
    objectToCoreSRealization_localized_isIso X.carrier
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (objectCoreRealizationComparison.app X ≫ (coreSingleRealizationIso X).hom))
  rw [Functor.map_comp]
  infer_instance

/-- 二つの元の object/単回比較の積も局所化同型。 -/
lemma objectSingleComparison_tensor_localized_isIso (X Y : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (objectSingleComparison.app X ⊗ₘ objectSingleComparison.app Y)) := by
  have hX := objectSingleComparison_localized_isIso X
  have hY := objectSingleComparison_localized_isIso Y
  have := AnodyneHomotopy.whiskerRight_anodyneQ_isIso (objectSingleComparison.app X) hX
    (objectSConstructionFunctor.obj Y)
  have := AnodyneHomotopy.whiskerLeft_anodyneQ_isIso (objectSingleComparison.app Y) hY
    ((multiRealizationFunctor 1).obj X)
  rw [tensorHom_def, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

/-- object S の元の完全射対の同値性は、同じ二つの射の単回実現へ移る。 -/
lemma singlePair_localized_isIso_of_objectPair {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z)
    (h : IsIso (AnodyneHomotopy.anodyneQ.map
      (lift (objectSConstructionFunctor.map f) (objectSConstructionFunctor.map g)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (lift ((multiRealizationFunctor 1).map f) ((multiRealizationFunctor 1).map g))) := by
  have he : lift (objectSConstructionFunctor.map f) (objectSConstructionFunctor.map g) ≫
      (objectSingleComparison.app Y ⊗ₘ objectSingleComparison.app Z) =
        objectSingleComparison.app X ≫
          lift ((multiRealizationFunctor 1).map f) ((multiRealizationFunctor 1).map g) := by
    rw [lift_map, comp_lift, objectSingleComparison.naturality f,
      objectSingleComparison.naturality g]
  have := objectSingleComparison_tensor_localized_isIso Y Z
  have := objectSingleComparison_localized_isIso X
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map (objectSingleComparison.app X) ≫
      AnodyneHomotopy.anodyneQ.map
        (lift ((multiRealizationFunctor 1).map f) ((multiRealizationFunctor 1).map g))) := by
    rw [← Functor.map_comp, ← he, Functor.map_comp]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hi

end SerrePositivity.KST.Fibration
