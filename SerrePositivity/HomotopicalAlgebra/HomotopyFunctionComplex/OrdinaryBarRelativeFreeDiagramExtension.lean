module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension

/-! # Extend free diagrams while fixing prescribed generators over the whole parameter

Prescribed generators and every path composed of them are retained. This
is a relative free-diagram lifting statement, not lifting for arbitrary
categories with relations or a strict section of the original base.
-/

@[expose] public section
universe v u uV vV
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension
open OrdinaryBarFreeDiagramExtension
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {V : Type uV} [Quiver.{vV} V] {T U : SSet.{max u v}} (j : U ⟶ T) [Mono j]

structure Prescribed (φ : V ⥤q target (C := C) hcof hfib U) where
  fixed : {X Y : V} → (X ⟶ Y) → Prop
  value : {X Y : V} → (e : X ⟶ Y) → fixed e →
    (liftedObject hcof hfib (T := T) (φ.obj X) ⟶ liftedObject hcof hfib (T := T) (φ.obj Y))
  restriction : ∀ {X Y : V} (e : X ⟶ Y) (he : fixed e),
    (OrdinaryBarChoiceCategory.reindex hcof hfib j).map (value e he) = φ.map e

variable (φ : V ⥤q target (C := C) hcof hfib U) (P : Prescribed hcof hfib j φ)

def edge {X Y : V} (e : X ⟶ Y) :
    liftedObject hcof hfib (T := T) (φ.obj X) ⟶ liftedObject hcof hfib (T := T) (φ.obj Y) := by
  classical
  exact if he : P.fixed e then P.value e he else edgeLift hcof hfib j φ e

lemma edge_restriction {X Y : V} (e : X ⟶ Y) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib j).map (edge hcof hfib j φ P e) = φ.map e := by
  classical
  unfold edge
  split_ifs with he
  · exact P.restriction e he
  · exact edgeLift_fac hcof hfib j φ e

lemma edge_fixed {X Y : V} (e : X ⟶ Y) (he : P.fixed e) :
    edge hcof hfib j φ P e = P.value e he := by
  classical
  exact dite_eq_left he

def generators : V ⥤q target (C := C) hcof hfib T where
  obj X := liftedObject hcof hfib (T := T) (φ.obj X)
  map e := edge hcof hfib j φ P e

def extend : Paths V ⥤ target (C := C) hcof hfib T :=
  Paths.lift (generators hcof hfib j φ P)

lemma extend_restriction :
    extend hcof hfib j φ P ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib j = Paths.lift φ := by
  refine Paths.ext_functor
    (F := extend hcof hfib j φ P ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib j)
    (G := Paths.lift φ) rfl ?_
  intro X Y e
  simp only [CategoryTheory.Functor.comp_map, extend, Paths.lift_toPath,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  exact edge_restriction hcof hfib j φ P e

lemma extend_fixed {X Y : V} (e : X ⟶ Y) (he : P.fixed e) :
    (extend hcof hfib j φ P).map e.toPath = P.value e he := by
  change (Paths.lift (generators hcof hfib j φ P)).map e.toPath = _
  rw [Paths.lift_toPath]
  exact edge_fixed hcof hfib j φ P e he

def AllFixed {X : V} : {Y : V} → Quiver.Path X Y → Prop
  | _, .nil => True
  | _, .cons q e => AllFixed q ∧ P.fixed e

def prescribedPath {X : V} : {Y : V} → (q : Quiver.Path X Y) → AllFixed hcof hfib j φ P q →
    (liftedObject hcof hfib (T := T) (φ.obj X) ⟶ liftedObject hcof hfib (T := T) (φ.obj Y))
  | _, .nil, _ => 𝟙 _
  | _, .cons q e, h => prescribedPath q h.1 ≫ P.value e h.2

lemma extend_fixed_path {X Y : V} (q : Quiver.Path X Y)
    (hq : AllFixed hcof hfib j φ P q) :
    (extend hcof hfib j φ P).map q = prescribedPath hcof hfib j φ P q hq := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    change (extend hcof hfib j φ P).map q ≫ edge hcof hfib j φ P e = _
    rw [ih hq.1, edge_fixed hcof hfib j φ P e hq.2]
    rfl

lemma extend_projection :
    extend hcof hfib j φ P ⋙ OrdinaryBarChoiceCategory.projection hcof hfib T =
      Paths.lift φ ⋙ OrdinaryBarChoiceCategory.projection hcof hfib U := by
  have h := congrArg (fun F => F ⋙ OrdinaryBarChoiceCategory.projection hcof hfib U)
    (extend_restriction hcof hfib j φ P)
  simpa only [CategoryTheory.Functor.assoc, OrdinaryBarChoiceCategory.reindex_projection] using h

def extendFunctor (A : Paths V ⥤ target (C := C) hcof hfib U)
    (Q : Prescribed hcof hfib j (Paths.of V ⋙q A.toPrefunctor)) :
    Paths V ⥤ target (C := C) hcof hfib T :=
  extend hcof hfib j (Paths.of V ⋙q A.toPrefunctor) Q

lemma extendFunctor_restriction (A : Paths V ⥤ target (C := C) hcof hfib U)
    (Q : Prescribed hcof hfib j (Paths.of V ⋙q A.toPrefunctor)) :
    extendFunctor hcof hfib j A Q ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib j = A := by
  change extend hcof hfib j _ Q ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib j = A
  rw [extend_restriction]
  exact (Paths.lift_unique _ A rfl).symm

lemma extendFunctor_projection (A : Paths V ⥤ target (C := C) hcof hfib U)
    (Q : Prescribed hcof hfib j (Paths.of V ⋙q A.toPrefunctor)) :
    extendFunctor hcof hfib j A Q ⋙ OrdinaryBarChoiceCategory.projection hcof hfib T =
      A ⋙ OrdinaryBarChoiceCategory.projection hcof hfib U := by
  have h := congrArg (fun F => F ⋙ OrdinaryBarChoiceCategory.projection hcof hfib U)
    (extendFunctor_restriction hcof hfib j A Q)
  simpa only [CategoryTheory.Functor.assoc, OrdinaryBarChoiceCategory.reindex_projection] using h

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension
