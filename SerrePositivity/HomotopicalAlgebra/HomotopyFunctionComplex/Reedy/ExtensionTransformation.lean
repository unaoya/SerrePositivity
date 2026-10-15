module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionFunctor

/-! # Extending natural transformations over an attached Reedy object

A transformation below the new degree and a map on the attached objects
extend if they commute with incoming direct and outgoing inverse maps.
The resulting transformation is natural on every map of the new diagram.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.BoundaryExtension
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  {r : ReedyStructure inverse direct α} {j : J}
  {C : Type u'} [Category.{v'} C] {H K : Lower r (r.deg j) ⥤ C}
  (d : BoundaryExtension r j H) (e : BoundaryExtension r j K)

structure Map (τ : H ⟶ K) where
  hom : d.obj ⟶ e.obj
  incoming {x : Lower r (r.deg j)} (f : x.obj ⟶ j) (hf : direct f) :
    d.incoming f hf ≫ hom = τ.app x ≫ e.incoming f hf
  outgoing {x : Lower r (r.deg j)} (f : j ⟶ x.obj) (hf : inverse f) :
    d.outgoing f hf ≫ τ.app x = hom ≫ e.outgoing f hf

namespace Map
variable {d e} {τ : H ⟶ K} (m : Map d e τ)

abbrev app : ∀ x : Adjoin r j, d.object x ⟶ e.object x
  | none => m.hom
  | some x => τ.app x

lemma naturality_inverse {x y : Adjoin r j} (f : x ⟶ y) (hf : inverse f.hom) :
    d.toFunctor.map f ≫ m.app y = m.app x ≫ e.toFunctor.map f := by
  rw [d.toFunctor_map_inverse f hf, e.toFunctor_map_inverse f hf]
  cases x with
  | none =>
    cases y with
    | none => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | some y => exact m.outgoing f.hom hf
  | some x =>
    cases y with
    | none => exact (not_inverse_into_top r j x f.hom hf).elim
    | some y => exact τ.naturality (ObjectProperty.homMk f.hom)

lemma naturality_direct {x y : Adjoin r j} (f : x ⟶ y) (hf : direct f.hom) :
    d.toFunctor.map f ≫ m.app y = m.app x ≫ e.toFunctor.map f := by
  rw [d.toFunctor_map_direct f hf, e.toFunctor_map_direct f hf]
  cases x with
  | none =>
    cases y with
    | none => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | some y => exact (not_direct_from_top r j y f.hom hf).elim
  | some x =>
    cases y with
    | none => exact m.incoming f.hom hf
    | some y => exact τ.naturality (ObjectProperty.homMk f.hom)

def toNatTrans : d.toFunctor ⟶ e.toFunctor :=
  natTransOfReedy (adjoinReedy r j) m.app m.naturality_inverse m.naturality_direct

@[simp]
lemma toNatTrans_app_top : m.toNatTrans.app (none : Adjoin r j) = m.hom := rfl

@[simp]
lemma toNatTrans_app_lower (x : Lower r (r.deg j)) :
    m.toNatTrans.app (some x) = τ.app x := rfl

end Map
end SerrePositivity.Reedy.BoundaryExtension
