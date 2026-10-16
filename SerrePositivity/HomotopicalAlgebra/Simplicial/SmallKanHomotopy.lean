module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom

/-! # Small Kan values with small interval-homotopy-class morphisms

This is an ordinary category, not an enrichment or a strict simplicial
replacement of a diagram. Its universe-lift realization is fully faithful
in the large anodyne localization. No simplicial model structure is used.
-/

@[expose] public section
universe v w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SmallKanHomotopy

structure Object where
  value : SSet.{v}
  kan : SSet.modelCategoryQuillen.J.rlp (terminal.from value)

def comp {X Y Z : Object.{v}} (f : HomotopyClasses.obj X.value Y.value)
    (g : HomotopyClasses.obj Y.value Z.value) : HomotopyClasses.obj X.value Z.value :=
  Quot.liftOn f (fun f => HomotopyClasses.pre f g) (fun _ _ ⟨H⟩ => by
    refine Quot.inductionOn g (fun g => ?_)
    exact HomotopyClasses.sound (HomotopyClasses.postHomotopy g H))

instance : Category.{v} Object.{v} where
  Hom X Y := HomotopyClasses.obj X.value Y.value
  id X := HomotopyClasses.mk (𝟙 X.value)
  comp := comp
  id_comp f := by
    refine Quot.inductionOn f (fun f => ?_)
    exact congrArg HomotopyClasses.mk (Category.id_comp f)
  comp_id f := by
    refine Quot.inductionOn f (fun f => ?_)
    exact congrArg HomotopyClasses.mk (Category.comp_id f)
  assoc f g h := by
    refine Quot.inductionOn f (fun f => ?_)
    refine Quot.inductionOn g (fun g => ?_)
    refine Quot.inductionOn h (fun h => ?_)
    exact congrArg HomotopyClasses.mk (Category.assoc f g h)

variable {D : Type uD} [Category.{vD} D] (L : SSet.{max w v} ⥤ D)
  [L.IsLocalization SSet.anodyneExtensions]

def realization : Object.{v} ⥤ D where
  obj X := L.obj (UniverseLift.obj.{w} X.value)
  map {X Y} f := UniverseLift.smallLocalizedHomEquiv.{w, v} L X.value Y.value Y.kan f
  map_id X := by
    change L.map (SSet.uliftFunctor.{w, v}.map (𝟙 X.value)) = 𝟙 _
    rw [SSet.uliftFunctor.map_id, L.map_id]
  map_comp {X Y Z} f g := by
    refine Quot.inductionOn f (fun f => ?_)
    refine Quot.inductionOn g (fun g => ?_)
    change L.map (SSet.uliftFunctor.{w, v}.map (f ≫ g)) =
      L.map (SSet.uliftFunctor.{w, v}.map f) ≫ L.map (SSet.uliftFunctor.{w, v}.map g)
    rw [SSet.uliftFunctor.map_comp, L.map_comp]

def fullyFaithful : (realization.{v, w} L).FullyFaithful where
  preimage {X Y} f := (UniverseLift.smallLocalizedHomEquiv.{w, v} L X.value Y.value Y.kan).symm f
  map_preimage {X Y} f :=
    (UniverseLift.smallLocalizedHomEquiv.{w, v} L X.value Y.value Y.kan).apply_symm_apply f
  preimage_map {X Y} f :=
    (UniverseLift.smallLocalizedHomEquiv.{w, v} L X.value Y.value Y.kan).symm_apply_apply f

end SerrePositivity.SimplicialModel.SmallKanHomotopy
