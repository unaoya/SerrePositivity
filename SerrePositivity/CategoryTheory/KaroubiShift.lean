module

public import SerrePositivity.CategoryTheory.KaroubiLinear
public import Mathlib.CategoryTheory.Shift.Induced
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # Karoubi 包絡上のシフトと標準包含の両立 -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Idempotents

variable (C : Type*) [Category* C] [HasShift C ℤ]

/-- シフト関手を各冪等元へ適用して得るシフト。 -/
noncomputable instance karoubiHasShift : HasShift (Karoubi C) ℤ :=
  HasShift.induced (toKaroubi C) ℤ
    (fun n ↦ (functorExtension₂ C C).obj (shiftFunctor C n))
    (fun n ↦ (functorExtension₂CompWhiskeringLeftToKaroubiIso C C).app (shiftFunctor C n))

noncomputable instance toKaroubi_commShift : (toKaroubi C).CommShift ℤ :=
  Functor.CommShift.ofInduced (toKaroubi C) ℤ
    (fun n ↦ (functorExtension₂ C C).obj (shiftFunctor C n))
    (fun n ↦ (functorExtension₂CompWhiskeringLeftToKaroubiIso C C).app (shiftFunctor C n))

@[simp] lemma toKaroubi_commShift_hom_f (X : C) (n : ℤ) :
    (((toKaroubi C).commShiftIso n).hom.app X).f = 𝟙 (X⟦n⟧) := rfl

@[simp] lemma toKaroubi_commShift_inv_f (X : C) (n : ℤ) :
    (((toKaroubi C).commShiftIso n).inv.app X).f = 𝟙 (X⟦n⟧) := rfl

/-- Karoubi シフトの対象は元の対象と冪等元のシフト。 -/
@[simp] lemma karoubi_shift_X (P : Karoubi C) (n : ℤ) :
    (P⟦n⟧).X = P.X⟦n⟧ := rfl

@[simp] lemma karoubi_shift_p (P : Karoubi C) (n : ℤ) :
    (P⟦n⟧).p = P.p⟦n⟧' := rfl

@[simp] lemma karoubi_shift_map_f {P Q : Karoubi C} (f : P ⟶ Q) (n : ℤ) :
    (f⟦n⟧').f = f.f⟦n⟧' := rfl

variable [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]

open CategoryTheory.Limits in
open scoped ZeroObject in
instance karoubiHasZeroObject [HasZeroObject C] : HasZeroObject (Karoubi C) :=
  ⟨⟨(toKaroubi C).obj 0, (toKaroubi C).map_isZero (isZero_zero C)⟩⟩

instance karoubi_shift_additive (n : ℤ) : (shiftFunctor (Karoubi C) n).Additive :=
  inferInstanceAs (((functorExtension₂ C C).obj (shiftFunctor C n)).Additive)

instance karoubi_shift_linear {R : Type*} [Semiring R] [Linear R C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (n : ℤ) :
    (shiftFunctor (Karoubi C) n).Linear R :=
  inferInstanceAs (((functorExtension₂ C C).obj (shiftFunctor C n)).Linear R)

end SerrePositivity
