module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionDegreeTwo

/-! # The exact intersection of the two degree-two degeneracy generator images

A path duplicated from the original category can be a singleton only if
both its preimage and its inner singleton are the same original generator.
The counit gives strict, actual recovery of all preimages.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreePathDegeneracyImage
open FreePathResolution
variable {C : Type u} [Category.{v} C]

lemma toPath_injective {V : Type*} [Quiver V] {X Y : V} :
    Function.Injective (fun f : X ⟶ Y => f.toPath) := by
  intro f g h
  cases h
  rfl

lemma duplicate_length {X Y : C} (p : Quiver.Path X Y) :
    ((duplicate C).map p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p f ih =>
    change ((duplicate C).map p).length + 1 = p.length + 1
    exact congrArg Nat.succ ih

lemma singleton_of_length_one {V : Type*} [Quiver V] {X Y : V} (p : Quiver.Path X Y)
    (h : p.length = 1) : ∃ f : X ⟶ Y, p = f.toPath := by
  cases p with
  | nil => simp at h
  | @cons Z Y p f =>
    have hp : p.length = 0 := by simpa only [Quiver.Path.length_cons, Nat.add_eq_right] using h
    obtain rfl := Quiver.Path.eq_of_length_zero p hp
    obtain rfl := Quiver.Path.eq_nil_of_length_zero p hp
    exact ⟨f, rfl⟩

lemma duplicate_eq_singleton {X Y : C} (p q : Quiver.Path X Y)
    (h : (duplicate C).map p = Quiver.Hom.toPath (V := Paths C) q) :
    ∃ f : X ⟶ Y, p = f.toPath ∧ q = f.toPath := by
  have hp : p.length = 1 := by
    have hl := congrArg Quiver.Path.length h
    simpa only [duplicate_length, Quiver.Path.length_toPath] using hl
  obtain ⟨f, rfl⟩ := singleton_of_length_one p hp
  rw [duplicate_generator] at h
  exact ⟨f, rfl, (toPath_injective h).symm⟩

lemma duplicate_map_injective {X Y : C} : Function.Injective
    (fun p : Quiver.Path X Y => (duplicate C).map p) := by
  intro p q h
  have hh := congrArg (counit (Paths C)).map h
  have hp := congr($(left_counit (C := C)).map p)
  have hq := congr($(left_counit (C := C)).map q)
  exact hp.symm.trans (hh.trans hq)

lemma counit_duplicate {X Y : C} (p : Quiver.Path X Y) :
    (counit (Paths C)).map ((duplicate C).map p) = p :=
  congr($(left_counit (C := C)).map p)

/-- Both types of degenerate generators have a common image exactly at double singletons. -/
lemma generator_image_intersection {X Y : C} (p q : Quiver.Path X Y) :
    Quiver.Hom.toPath (V := Paths C) q = (duplicate C).map p ↔
      ∃ f : X ⟶ Y, p = f.toPath ∧ q = f.toPath := by
  constructor
  · intro h
    exact duplicate_eq_singleton p q h.symm
  · rintro ⟨f, rfl, rfl⟩
    exact (duplicate_generator f).symm

end SerrePositivity.HomotopyFunctionComplex.FreePathDegeneracyImage
