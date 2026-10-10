module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Shift.Linear

/-! # シフトで安定な充満部分圏の線形構造 -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C]
  [Linear R C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  (P : ObjectProperty C) [P.IsStableUnderShift ℤ]

/-- 充満部分圏のシフトは、元の圏のシフトの線形性を引き継ぐ。 -/
instance fullSubcategory_shift_linear (n : ℤ) :
    (shiftFunctor P.FullSubcategory n).Linear R := by
  have : (shiftFunctor P.FullSubcategory n ⋙ P.ι).Linear R :=
    Functor.linear_of_iso R (P.ι.commShiftIso n).symm
  constructor
  intro X Y f a
  apply P.ι.map_injective
  simpa only [Functor.map_smul, Functor.comp_map] using
    (shiftFunctor P.FullSubcategory n ⋙ P.ι).map_smul a f

end SerrePositivity
