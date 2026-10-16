module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory
public import Mathlib.CategoryTheory.PathCategory.Basic

/-! # Extend whole free diagrams while preserving every prescribed parameter

The source is the auxiliary free category on an arbitrary quiver. The
original source model remains arbitrary. Generation gives strict functors
without assuming a strict section over a category with relations.
-/

@[expose] public section
universe v u uV vV
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {V : Type uV} [Quiver.{vV} V] {T U : SSet.{max u v}} (j : U ⟶ T) [Mono j]

abbrev target (P : SSet.{max u v}) := OrdinaryBarChoiceCategory.Object (C := C) hcof hfib P

def liftedObject (X : target (C := C) hcof hfib U) : target (C := C) hcof hfib T := ⟨X.base⟩

def edgeLift (φ : V ⥤q target (C := C) hcof hfib U) {X Y : V} (e : X ⟶ Y) :
    liftedObject hcof hfib (T := T) (φ.obj X) ⟶ liftedObject hcof hfib (T := T) (φ.obj Y) :=
  (OrdinaryBarChoiceCategory.reindex_map_surjective hcof hfib j
    (liftedObject hcof hfib (T := T) (φ.obj X))
    (liftedObject hcof hfib (T := T) (φ.obj Y)) (φ.map e)).choose

lemma edgeLift_fac (φ : V ⥤q target (C := C) hcof hfib U) {X Y : V} (e : X ⟶ Y) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib j).map (edgeLift hcof hfib j φ e) = φ.map e :=
  (OrdinaryBarChoiceCategory.reindex_map_surjective hcof hfib j
    (liftedObject hcof hfib (T := T) (φ.obj X))
    (liftedObject hcof hfib (T := T) (φ.obj Y)) (φ.map e)).choose_spec

def generators (φ : V ⥤q target (C := C) hcof hfib U) : V ⥤q target (C := C) hcof hfib T where
  obj X := liftedObject hcof hfib (T := T) (φ.obj X)
  map e := edgeLift hcof hfib j φ e

def extend (φ : V ⥤q target (C := C) hcof hfib U) : Paths V ⥤ target (C := C) hcof hfib T :=
  Paths.lift (generators hcof hfib j φ)

lemma extend_generator (φ : V ⥤q target (C := C) hcof hfib U) {X Y : V} (e : X ⟶ Y) :
    (extend hcof hfib j φ).map e.toPath = edgeLift hcof hfib j φ e :=
  Paths.lift_toPath _ e

lemma extend_restriction (φ : V ⥤q target (C := C) hcof hfib U) :
    extend hcof hfib j φ ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib j = Paths.lift φ := by
  refine Paths.ext_functor
    (F := extend hcof hfib j φ ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib j)
    (G := Paths.lift φ) rfl ?_
  intro X Y e
  simp only [CategoryTheory.Functor.comp_map, extend_generator, Paths.lift_toPath,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  exact edgeLift_fac hcof hfib j φ e

lemma extend_projection (φ : V ⥤q target (C := C) hcof hfib U) :
    extend hcof hfib j φ ⋙ OrdinaryBarChoiceCategory.projection hcof hfib T =
      Paths.lift φ ⋙ OrdinaryBarChoiceCategory.projection hcof hfib U := by
  have h := congrArg (fun F => F ⋙ OrdinaryBarChoiceCategory.projection hcof hfib U)
    (extend_restriction hcof hfib j φ)
  simpa only [CategoryTheory.Functor.assoc, OrdinaryBarChoiceCategory.reindex_projection] using h

def extendFunctor (A : Paths V ⥤ target (C := C) hcof hfib U) :
    Paths V ⥤ target (C := C) hcof hfib T :=
  extend hcof hfib j (Paths.of V ⋙q A.toPrefunctor)

lemma extendFunctor_restriction (A : Paths V ⥤ target (C := C) hcof hfib U) :
    extendFunctor hcof hfib j A ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib j = A := by
  rw [extendFunctor, extend_restriction]
  exact (Paths.lift_unique _ A rfl).symm

lemma extendFunctor_projection (A : Paths V ⥤ target (C := C) hcof hfib U) :
    extendFunctor hcof hfib j A ⋙ OrdinaryBarChoiceCategory.projection hcof hfib T =
      A ⋙ OrdinaryBarChoiceCategory.projection hcof hfib U := by
  have h := congrArg (fun F => F ⋙ OrdinaryBarChoiceCategory.projection hcof hfib U)
    (extendFunctor_restriction hcof hfib j A)
  simpa only [CategoryTheory.Functor.assoc, OrdinaryBarChoiceCategory.reindex_projection] using h

def emptyGenerators (φ : V ⥤q (Cᵒᵖ × C)) :
    V ⥤q target (C := C) hcof hfib (⊥_ SSet.{max u v}) where
  obj X := ⟨φ.obj X⟩
  map e := ⟨φ.map e, Limits.initial.to _⟩

def liftBaseGenerators (φ : V ⥤q (Cᵒᵖ × C)) (P : SSet.{max u v}) :
    Paths V ⥤ target (C := C) hcof hfib P :=
  extend hcof hfib (Limits.initial.to P) (emptyGenerators hcof hfib φ)

lemma liftBaseGenerators_projection (φ : V ⥤q (Cᵒᵖ × C)) (P : SSet.{max u v}) :
    liftBaseGenerators hcof hfib φ P ⋙ OrdinaryBarChoiceCategory.projection hcof hfib P =
      Paths.lift φ := by
  rw [liftBaseGenerators, extend_projection]
  refine Paths.ext_functor
    (F := Paths.lift (emptyGenerators hcof hfib φ) ⋙
      OrdinaryBarChoiceCategory.projection hcof hfib _)
    (G := Paths.lift φ) rfl ?_
  intro X Y e
  simp only [CategoryTheory.Functor.comp_map, Paths.lift_toPath, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  rfl

def liftBase (F : Paths V ⥤ (Cᵒᵖ × C)) (P : SSet.{max u v}) :
    Paths V ⥤ target (C := C) hcof hfib P :=
  liftBaseGenerators hcof hfib (Paths.of V ⋙q F.toPrefunctor) P

lemma liftBase_projection (F : Paths V ⥤ (Cᵒᵖ × C)) (P : SSet.{max u v}) :
    liftBase hcof hfib F P ⋙ OrdinaryBarChoiceCategory.projection hcof hfib P = F := by
  rw [liftBase, liftBaseGenerators_projection]
  exact (Paths.lift_unique _ F rfl).symm

def freeCover (P : SSet.{max u v}) : Paths (Cᵒᵖ × C) ⥤ target (C := C) hcof hfib P :=
  liftBaseGenerators hcof hfib (𝟭q (Cᵒᵖ × C)) P

lemma freeCover_projection (P : SSet.{max u v}) :
    freeCover (C := C) hcof hfib P ⋙ OrdinaryBarChoiceCategory.projection hcof hfib P =
      Paths.lift (𝟭q (Cᵒᵖ × C)) :=
  liftBaseGenerators_projection hcof hfib _ P

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension
