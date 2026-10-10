module

public import SerrePositivity.HomologicalAlgebra.NullHomotopy
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# スカラーの共通の冪による台の条件

線形三角圏で、指定されたスカラーが共通の正の冪で恒等射を零にする対象を扱う。
直和因子・シフト・完全三角形への安定性を示す。
元の圏と局所化後の圏の双方で使える定義であり、両者の台は区別する。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C]
  [Linear R C] {ι : Type*} (z : ι → R)

/-- 指定されたスカラーの共通の正の冪が対象の恒等射を零にする条件。 -/
def scalarSupported : ObjectProperty C :=
  fun X ↦ ∃ v : ℕ, 0 < v ∧ ∀ j, z j ^ v • 𝟙 X = 0

/-- 台の条件は直和因子に移る。消去指数は増やさなくてよい。 -/
instance : (scalarSupported (C := C) z).IsStableUnderRetracts where
  of_retract {X Y} r hY := by
    obtain ⟨v, hv, h⟩ := hY
    refine ⟨v, hv, fun j ↦ ?_⟩
    have he : z j ^ v • 𝟙 X = r.i ≫ (z j ^ v • 𝟙 Y) ≫ r.r := by simp
    rw [he, h j, zero_comp, comp_zero]

variable [HasZeroObject C]

instance : (scalarSupported (C := C) z).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, 1, by omega,
    fun _ ↦ (isZero_zero C).eq_of_src _ _⟩

omit [HasZeroObject C] in
/-- 線形関手は台の条件を保存する。 -/
lemma scalarSupported_map {D : Type*} [Category* D] [Preadditive D] [Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C) (hX : scalarSupported z X) :
    scalarSupported z (F.obj X) := by
  obtain ⟨v, hv, h⟩ := hX
  refine ⟨v, hv, fun j ↦ ?_⟩
  simpa only [F.map_smul, F.map_id, F.map_zero] using congrArg F.map (h j)

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]

instance : (scalarSupported (C := C) z).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift X hX := (ObjectProperty.prop_shift_iff _ _ _).2
        (scalarSupported_map z (shiftFunctor C n) X hX) }

/-- 完全三角形の初めの二対象の消去指数をそろえ、その二倍を錐の指数に使う。 -/
lemma scalarSupported_triangle (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : scalarSupported z T.obj₁) (h₂ : scalarSupported z T.obj₂) :
    scalarSupported z T.obj₃ := by
  obtain ⟨v, hv, h₁⟩ := h₁
  obtain ⟨w, hw, h₂⟩ := h₂
  refine ⟨max v w + max v w, by omega, fun j ↦ ?_⟩
  rw [pow_add]
  apply smul_mul_self_id_eq_zero T hT
  · rw [pow_smul_id_eq_zero_of_le (h₂ j) (le_max_right v w), zero_comp]
  · rw [pow_smul_id_eq_zero_of_le (h₁ j) (le_max_left v w),
      Functor.map_zero, comp_zero]

instance : (scalarSupported (C := C) z).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (scalarSupported_triangle z)

instance : (scalarSupported (C := C) z).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

end SerrePositivity
